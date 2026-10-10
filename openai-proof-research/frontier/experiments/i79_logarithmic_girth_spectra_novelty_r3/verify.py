"""Offline read-only provenance/search/exact diagnostic replay. No analytic verdict."""
import sys
sys.dont_write_bytecode=True
import pathlib,json,hashlib,re,subprocess,concurrent.futures
from collections import Counter
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3';E=R/'frontier/experiments/i79_logarithmic_girth_spectra_novelty_r3'
REPORT='frontier/reviews/i79-logarithmic-girth-spectra-novelty-r3.md'
LEDGERS={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def check(c,m):
 if not c:raise AssertionError(m)
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def main():
 preseal='--preseal' in sys.argv
 if not preseal:
  seal=read(S/'seal-v1.json');check(set(seal['mutable_ledgers'])==LEDGERS,'drift allowlist')
  excluded={str(S.relative_to(R)/'seal-v1.json'),str(E.relative_to(R)/'verification.json')}
  check(set(seal['exclusions'])==excluded,'exclusion allowlist')
  actual={REPORT}|{str(p.relative_to(R)) for base in (S,E) for p in base.rglob('*') if p.is_file()}
  check(actual-excluded=={x['path'] for x in seal['artifacts']},'seal artifact domain')
  for x in seal['artifacts']:
   b=(R/x['path']).read_bytes();check(sha(b)==x['sha256'] and len(b)==x['bytes'],'sealed '+x['path'])
 drift=[]
 for x in read(S/'inputs.json'):
  check(x['mutable']==(x['path'] in LEDGERS),'reference mutability')
  b=(R/x['path']).read_bytes();good=sha(b)==x['sha256'] and len(b)==x['bytes']
  if x['mutable']:
   snap=(S/'ledgers'/x['path'].replace('/','__')).read_bytes();check(sha(snap)==x['sha256'],'ledger snapshot')
   if not good:drift.append(x['path'])
  else:check(good,'immutable reference '+x['path'])
 brief=(S/'full-brief.txt').read_text();prov=read(S/'brief-provenance.json')
 check(len(brief.encode('utf-16-le'))//2==prov['utf16Length']+1,'complete exact brief length')
 check(sum(prov['slices'])==prov['utf16Length'],'brief contiguous slices')
 check('--- FINAL PARENT I76 REPLAY ---' in brief and '--- ORIGINAL I76 REPORT ---' in brief,'brief includes original and parent')
 for x in read(S/'passages.json')+read(S/'versions.json'):
  b=''.join((R/x['path']).read_text().splitlines(keepends=True)[x['start']-1:x['end']]).encode()
  check(sha(b)==x['sha256'] and b.decode()==x['text'],'passage '+x.get('id',x['path']))
 tree=read(R/'sources/preprints-tree.json')['tree'];blobs={x['path']:x for x in tree if x['type']=='blob'}
 check(len(tree)==13223 and len(blobs)==10373 and len({x['path'].split('/')[1] for x in tree})==749,'complete tree')
 old=read(R/'frontier/sources/i72_graph_probability_discovery/corpus-domain.json');C=R/old['root']
 listing={str(pathlib.Path(p).relative_to(C)) for p in subprocess.check_output(['rg','--files','--no-ignore',str(C)],text=True).splitlines()}
 check(listing=={x['path'] for x in old['files']} and len(listing)==9340,'9340 fixed domain')
 for x in old['files']:
  b=(C/x['path']).read_bytes();check(blob(b)==blobs[x['path']]['sha']==x['git_blob'] and sha(b)==x['sha256'],'corpus identity '+x['path'])
 outside=[json.loads(l) for l in (S/'outside-requests.jsonl').read_text().splitlines()]
 check({x['path'] for x in outside}==set(blobs)-listing and len(outside)==1033,'remaining 1033 blobs exactly')
 pdfpairs=[]
 for x in outside:
  check('error' not in x and x['status']==200 and x['git_match'],'outside acquisition '+x['path'])
  b=(R/x['local']).read_bytes();check(blob(b)==blobs[x['path']]['sha'] and sha(b)==x['sha256'],'outside body')
  check(x['url'].startswith('https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'),'pinned raw URL')
  if 'extraction' in x:
   y=x['extraction'];check(y['code']==0 and sha((R/y['path']).read_bytes())==y['sha256'],'outside text');pdfpairs.append((R/x['local'],R/y['path']))
 requests=read(S/'primary-requests.json')+read(S/'primary-requests-2.json')
 for x in requests:
  check('error' not in x and x['status']==200,'primary acquisition')
  p=R/x['path'];b=p.read_bytes();check(sha(b)==x['sha256'] and len(b)==x['bytes'],'primary bytes')
  if 'extraction' in x:
   check(x['extraction']['code']==0,'primary extraction');pdfpairs.append((p,p.with_suffix('.txt')))
 def pdf(pair):
  p,t=pair;o=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True)
  check(o.returncode==0 and o.stdout==t.read_bytes(),'PDF extraction replay '+str(p));return 1
 with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:pdfcount=sum(pool.map(pdf,pdfpairs))
 searches=read(S/'searches.json')+[read(S/'search-additional.json')];patterns=[re.compile(x['pattern']) for x in searches];hits=[[] for x in searches]
 dom=read(S/'search-domain.json');check(len(dom)==10373 and {x['path'] for x in dom}==set(blobs),'search covers all blobs')
 outside_by={x['path']:x for x in outside}
 for x in dom:
  expected=C/x['path'] if x['path'] in listing else R/outside_by[x['path']].get('extraction',{}).get('path',outside_by[x['path']]['local'])
  check(R/x['local']==expected,'search extraction/body mapping')
  b=expected.read_bytes();check(sha(b)==x['sha256'],'search body')
  for i,l in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
   for j,rx in enumerate(patterns):
    if rx.search(l):hits[j].append((x['path'],i,l,x['kind']))
 for x,h in zip(searches,hits):check(Counter(h)==Counter(map(tuple,x['hits'])),'search multiset '+x['label'])
 out=subprocess.run([sys.executable,'-B',str(E/'diagnostics.py')],capture_output=True,text=True,cwd=R);check(out.returncode==0,'I79 finite diagnostics '+out.stderr);check(json.loads(out.stdout)==read(E/'results.json'),'I79 diagnostic replay')
 out=subprocess.run([sys.executable,'-B','frontier/experiments/i76_logarithmic_girth_spectra/verify.py'],capture_output=True,text=True,cwd=R);check(out.returncode==0,'I76 replay '+out.stdout+out.stderr);prior=json.loads(out.stdout)
 captured=read(E/'i76-replay.json');check(prior['status']==captured['status'],'retained I76 status')
 for p in ('frontier/experiments/i72-parent-verification.json','frontier/experiments/i76-parent-verification.json'):check(read(R/p)['exit_code']==0,'parent wrapper status')
 print(json.dumps(dict(status='PASS_EVIDENCE_AND_EXACT_BOOKKEEPING_ONLY',preseal=preseal,read_only=True,analytic_status='Original I76 correctness not decided; I78 objections remain separate.',conditional_contribution={'A':'TECHNICAL','B':'TECHNICAL','package':'TECHNICAL'},count_change=False,sealed_artifacts=None if preseal else len(seal['artifacts']),immutable_inputs=sum(not x['mutable'] for x in read(S/'inputs.json')),mutable_ledger_drift=drift,corpus_files=9340,outside_blobs=1033,pdf_replays=pdfcount,primary_http_responses=len(requests),passages=len(read(S/'passages.json')),capture_versions={pathlib.Path(x['path']).name:x['latest'] for x in read(S/'versions.json')},search_line_multisets={x['label']:len(h) for x,h in zip(searches,hits)},i76_replay_status=prior['status']),indent=2,sort_keys=True))
if __name__=='__main__':
 try:main()
 except Exception as e:print(json.dumps({'status':'FAIL','error':str(e)},indent=2));sys.exit(1)
