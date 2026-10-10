"""I83 OFFLINE READ-ONLY verifier. No fetching, file writes, extraction-to-file or resealing."""
from pathlib import Path
import hashlib,json,subprocess,sys,re
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i83_catalan_finite_measure';E=R/'frontier/experiments/i83_catalan_finite_measure';REPORT=R/'frontier/iterations/i83-catalan-finite-measure.md'
I81='181eef41b4660773b4a8431177e7e979490f69431bc66b538e2b7986bcb3888e'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return (R/p).read_bytes()
def check(b,msg):
 if not b:raise AssertionError(msg)
def run(args):
 p=subprocess.run(args,cwd=R,capture_output=True)
 check(p.returncode in (0,1) if args[0]=='rg' else p.returncode==0,str(args[:3])+': '+p.stderr.decode(errors='replace'))
 return p.stdout
preflight=sys.argv[1:]==['--preflight']
check(preflight or len(sys.argv)==1 or (len(sys.argv)==3 and sys.argv[1]=='--expect-seal-sha256'),'usage: verify.py [--preflight | --expect-seal-sha256 HEX]')
paths=[p for base in [S,E] for p in base.rglob('*') if p.is_file()]+[REPORT]
check(all(not p.is_symlink() for p in paths),'symlink in owned domain')
actual={str(p.relative_to(R)) for p in paths if p!=S/'seal.json'}
if not preflight:
 raw=(S/'seal.json').read_bytes();seal=json.loads(raw)
 if len(sys.argv)==3:check(sha(raw)==sys.argv[2],'external seal digest mismatch')
 check(actual=={x['path'] for x in seal['artifacts']},'owned exact path set differs')
 for x in seal['artifacts']:
  b=read(x['path']);check(len(b)==x['bytes'] and sha(b)==x['sha256'],'owned bytes differ: '+x['path'])
refs=json.loads((S/'immutable-references.json').read_text())
for x in refs:
 b=read(x['path']);check(len(b)==x['bytes'] and sha(b)==x['sha256'],'immutable reference differs: '+x['path'])
# Bound original verifier is independently read-only and checks full 10,373-blob domain.
old=json.loads(run([sys.executable,'-B',str(R/'frontier/experiments/i81_diophantine_approximation_discovery/verify.py'),'--expect-seal-sha256',I81]))
check(old['evidence']=='PASS' and old['pinned_blobs']==10373 and old['outside_originals']==1033,'I81/full-domain replay')
base=json.loads((S/'i81-replay.json').read_text())
check({k:v for k,v in old.items() if k!='mutable_ledger_drift_informational'}=={k:v for k,v in base.items() if k!='mutable_ledger_drift_informational'},'I81 baseline changed apart from allowed drift')
rows=json.loads(read('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json'))
counts={}
for name in ['corpus','history']:
 d=json.loads((S/(name+'-search-definition.json')).read_text());files=d['files'];out=[]
 if name=='corpus':check(files==[x['local'] for x in rows],'exact complete search domain')
 for i in range(0,len(files),150):
  raw=run(['rg',*d['flags'],d['pattern'],*files[i:i+150]])
  for line in raw.split(b'\n'):
   if line:
    x=json.loads(line)
    if x['type']=='match':
     z=x['data'];out.append({'path':z['path']['text'],'line':z['line_number'],'text':z['lines']['text']})
 out.sort(key=lambda x:(x['path'],x['line'],x['text']))
 check(out==json.loads((S/(name+'-search-multiset.json')).read_text()),name+' exact multiset mismatch')
 counts[name]=len(out)
parent=json.loads((S/'corpus-search-multiset.json').read_text())
for name in ['focused','arithmetic']:
 d=json.loads((S/(name+'-filter.json')).read_text());got=[x for x in parent if re.search(d['pattern'],x['text'],re.I)]
 check(got==json.loads((S/(name+'-search-multiset.json')).read_text()),name+' explicit filter mismatch');counts[name]=len(got)
# Matched-family multiset from original broad search.
mp={x['local']:x['path'] for x in rows};families={}
for x in parent:
 f=mp[x['path']].split('/')[1];families[f]=families.get(f,0)+1
check(families==json.loads((S/'matched-families.json').read_text()),'matched families mismatch')
selected=json.loads((S/'selected-full-companions.json').read_text())
check(selected['files']==[x for x in rows if x['path'].split('/')[1] in selected['families']],'full selected companion coverage')
passages=json.loads((S/'passages.json').read_text())
for p in passages:
 b=b'\n'.join(read(p['path']).split(b'\n')[p['first']-1:p['last']]);check(sha(b)==p['sha256'],'passage mismatch: '+p['label'])
responses=[];pdfs=0
for f in ['primary-requests.jsonl','primary-requests-more.jsonl','primary-requests-rec.jsonl']:
 for line in (S/f).read_bytes().split(b'\n'):
  if not line:continue
  p=json.loads(line);responses.append(p);b=read(p['local']);check(sha(b)==p['sha256'] and len(b)==p['bytes'],'primary body binding')
  if 'extraction' in p:
   e=p['extraction'];check(p['status']==200 and e['code']==0 and b.startswith(b'%PDF'),'PDF status')
   check(sha(read(e['local']))==e['sha256'],'PDF retained text')
   check(sha(run(['pdftotext','-layout',str(R/p['local']),'-']))==e['sha256'],'PDF stdout extraction replay');pdfs+=1
for v in json.loads((S/'versions.json').read_text()):
 found=sorted(set(re.findall(r'(?:2408\.15403|2609\.26354|1507\.05697|2604\.20741|2609\.04176|math/0201024)v\d+',read(v['path']).decode())))
 check(found==v['versions'],'version observation mismatch')
check(run([sys.executable,'-B',str(E/'diagnostics.py')])==(E/'diagnostics.json').read_bytes(),'exact diagnostic stdout changed')
check(run([sys.executable,'-B',str(E/'optional_source_diagnostics.py')])==(S/'optional-source-diagnostics.json').read_bytes(),'optional floating diagnostic stdout changed')
scope=json.loads((S/'read-scope.json').read_text());drift=[p for p in scope['mutable_ledgers'] if read(p)!=(S/'ledgers'/p).read_bytes()]
print(json.dumps({'evidence':'PRESEAL CHECKS PASS; owned bytes not sealed' if preflight else 'PASS provenance and finite replay only','original_I81_A_B_criterion':'PASS ORIGINAL WITHOUT REPAIRS (scoped analytic review, not implied by this program)','C81':'GAP; unproved and unrefuted','contribution':'TECHNICAL partials; no substantial nomination','owned_artifacts':len(actual),'immutable_references':len(refs),'passages':len(passages),'pinned_blobs_checked_via_bound_I81_verifier':old['pinned_blobs'],'outside_originals':old['outside_originals'],'full_selected_companion_files':len(selected['files']),'search_records':counts,'new_primary_responses':len(responses),'new_primary_failures_retained':sum(p['status']!=200 for p in responses),'new_pdf_stdout_replays':pdfs,'inherited_primary_responses':old['primary_responses'],'inherited_pdf_stdout_replays':old['primary_pdf_replays'],'mutable_ledger_drift_informational':drift,'seal_sha256':None if preflight else sha((S/'seal.json').read_bytes())},indent=2,sort_keys=True))
