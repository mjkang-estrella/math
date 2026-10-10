"""Offline read-only I76 evidence and exact finite replay. Not a proof certificate."""
import sys
sys.dont_write_bytecode=True
import pathlib,json,hashlib,subprocess,re
from collections import Counter
R=pathlib.Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i76_logarithmic_girth_spectra'
E=R/'frontier/experiments/i76_logarithmic_girth_spectra'
REPORT='frontier/iterations/i76-logarithmic-girth-spectra.md'
LEDGERS={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def check(c,m):
 if not c:raise AssertionError(m)
def main():
 seal=read(S/'seal-v1.json')
 check(set(seal['mutable_ledgers'])==LEDGERS,'mutable allowlist')
 exclusions={str(S.relative_to(R)/'seal-v1.json'),str(E.relative_to(R)/'verification.json')}
 check(set(seal['exclusions'])==exclusions,'seal exclusions')
 actual={REPORT}|{str(p.relative_to(R)) for base in (S,E) for p in base.rglob('*') if p.is_file()}
 check(actual-exclusions=={x['path'] for x in seal['artifacts']},'assigned artifact domain differs from seal')
 for x in seal['artifacts']:
  b=(R/x['path']).read_bytes();check(sha(b)==x['sha256'] and len(b)==x['bytes'],'seal '+x['path'])
 drift=[]
 for x in read(S/'inputs.json'):
  check(x['mutable']==(x['path'] in LEDGERS),'reference mutability')
  b=(R/x['path']).read_bytes();good=sha(b)==x['sha256'] and len(b)==x['bytes']
  if x['mutable']:
   if not good:drift.append(x['path'])
  else:check(good,'immutable reference '+x['path'])
 brief=(S/'full-brief.txt').read_text();prov=read(S/'brief-provenance.json')
 expected=prov['utf16Length']+int(prov['fileFinalNewlineAdded'])
 check(len(brief.encode('utf-16-le'))//2==expected,'exact exported brief length')
 check((R/'frontier/iterations/i72-graph-probability-discovery.md').read_text().rstrip('\n') in brief,'full old report in frozen brief')
 tree={x['path']:x for x in read(R/'sources/preprints-tree.json')['tree'] if x['type']=='blob'}
 refs=read(S/'source-references.json')
 for x in refs:
  b=(R/x['local_path']).read_bytes()
  blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  check(len(b)==x['bytes'] and sha(b)==x['sha256'] and blob==x['git_blob']==tree[x['path']]['sha'],'source '+x['path'])
  check(x['raw_url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path'],'pinned URL')
 passages=read(S/'passages.json')
 for x in passages:
  b=''.join((R/x['path']).read_text().splitlines(keepends=True)[x['start']-1:x['end']]).encode()
  check(sha(b)==x['sha256'] and len(b)==x['bytes'],'passage '+x['id'])
 search=read(S/'interface-search.json');rx=re.compile(search['pattern']);hits=[]
 for p in search['domain']:
  for i,line in enumerate((R/p).read_text().splitlines(),1):
   if rx.search(line):hits.append((p,i,line))
 check(Counter(hits)==Counter(map(tuple,search['hits'])),'interface search line multiset')
 requests=read(S/'fresh-responses.json');pdfs=0
 for x in requests:
  check('error' not in x and x['status']==200,'fresh request '+x['name'])
  p=R/x['body_reference'];b=p.read_bytes()
  check(sha(b)==x['sha256'] and len(b)==x['bytes'],'response body '+x['name'])
  if x['name'].endswith('.pdf'):
   out=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True)
   check(out.returncode==0 and out.stdout==p.with_suffix('.txt').read_bytes(),'PDF text replay '+x['name']);pdfs+=1
 version=read(S/'version-binding.json');lines=(R/version['path']).read_text().splitlines(keepends=True)
 text=''.join(''.join(lines[a-1:b]) for a,b in version['ranges'])
 check(text==version['text'] and sha(text.encode())==version['sha256'] and '<strong>[v3]</strong>' in text,'HY capture-time version')
 old=subprocess.run([sys.executable,'-B','frontier/experiments/i72_graph_probability_discovery/verify.py'],cwd=R,capture_output=True,text=True)
 check(old.returncode==0,'old sealed evidence replay: '+old.stdout+old.stderr)
 oldresult=json.loads(old.stdout)
 parent=read(R/'frontier/experiments/i72-parent-verification.json')
 check(parent['exit_code']==0 and parent['result']['status']==oldresult['status'],'parent finalized verification')
 diagnostic=subprocess.run([sys.executable,'-B',str(E/'diagnostics.py')],cwd=R,capture_output=True,text=True)
 check(diagnostic.returncode==0,'I76 finite checks: '+diagnostic.stderr)
 check(json.loads(diagnostic.stdout)==read(E/'results.json'),'I76 exact finite output')
 print(json.dumps(dict(status='PASS_EVIDENCE_AND_FINITE_DIAGNOSTICS',read_only=True,
  analytic_status='Theorems A/B are author proof candidates, NOT independent original-proof approval. Literal CS is not asserted.',
  contribution_status='No acceptance or count change; B alone is technical. Fresh reviews required.',
  sealed_artifacts=len(seal['artifacts']),input_references=len(read(S/'inputs.json')),
  source_references=len(refs),passages=len(passages),fresh_responses=len(requests),pdf_replays=pdfs,
  current_HY_capture_version='v3',interface_search_multiset=len(hits),mutable_ledger_drift=drift,
  i72_replay=oldresult,finite_diagnostics='exact JSON reproduced'),indent=2,sort_keys=True))
if __name__=='__main__':
 try:main()
 except Exception as e:
  print(json.dumps({'status':'FAIL','error':str(e)},indent=2));sys.exit(1)
