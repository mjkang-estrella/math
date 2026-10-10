"""Offline, read-only evidence replay. Never updates sources, snapshots, or seals."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i72_graph_probability_discovery'
E=R/'frontier/experiments/i72_graph_probability_discovery'
LEDGERS={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def check(condition,message):
 if not condition:raise AssertionError(message)
def main():
 seal=read(S/'seal-v1.json');check(seal['mutable_ledgers']==sorted(LEDGERS),'mutable allowlist')
 for row in seal['artifacts']:
  p=R/row['path'];b=p.read_bytes();check(len(b)==row['bytes'] and sha(b)==row['sha256'],'seal '+row['path'])
 drift=[];refs=read(S/'inputs.json')['references']+read(S/'additional-references.json')
 for row in refs:
  b=(R/row['path']).read_bytes();good=sha(b)==row['sha256'] and len(b)==row['bytes']
  check(bool(row['mutable'])==(row['path'] in LEDGERS),'reference mutability '+row['path'])
  if row['mutable']:
   frozen=(R/row['snapshot']).read_bytes();check(sha(frozen)==row['sha256'] and len(frozen)==row['bytes'],'ledger snapshot')
   if not good:drift.append(row['path'])
  else:check(good,'immutable reference drift '+row['path'])
 tree=read(R/'sources/preprints-tree.json');blobs={r['path']:r for r in tree['tree'] if r['type']=='blob'}
 corpus=read(S/'corpus-domain.json');C=R/corpus['root'];domain=corpus['files'];paths={r['path'] for r in domain}
 listing={str(Path(p).relative_to(C)) for p in subprocess.check_output(['rg','--files','--no-ignore',str(C)],text=True).splitlines()};check(listing==paths,'fixed corpus domain changed')
 for row in domain:
  b=(C/row['path']).read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  check(len(b)==row['bytes'] and sha(b)==row['sha256'] and git==row['git_blob']==blobs[row['path']]['sha'],'corpus '+row['path'])
 inv=read(S/'inventory.json')
 check((len(tree['tree']),len(blobs),len(paths))==(inv['entries'],inv['blobs'],inv['fixed_corpus']),'inventory counts')
 check(len({r['path'].split('/')[1] for r in tree['tree']})==inv['manuscripts'],'manuscript count')
 check([e for p,e in sorted(blobs.items()) if p not in paths]==inv['other_blobs'],'remaining tree blobs')
 pinned=read(S/'pinned-manifest.json')
 for row in pinned:
  b=(S/'pinned'/row['path']).read_bytes();check(b==(C/row['path']).read_bytes(),'pinned corpus equality')
  check(sha(b)==row['sha256'] and row['git_blob']==blobs[row['path']]['sha'],'pinned identity')
  check(row['raw_url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+row['path'],'raw URL')
 search_counts={}
 for s in read(S/'searches.json'):
  rx=re.compile(s['pattern']);actual=[]
  for row in domain:
   for i,line in enumerate((C/row['path']).read_text(errors='replace').splitlines(),1):
    if rx.search(line):actual.append((row['path'],i,line))
  check(Counter(actual)==Counter(map(tuple,s['hits'])),'search multiset '+s['label']);search_counts[s['label']]=len(actual)
 passages=read(S/'passages.json');versions=read(S/'versions.json')
 for row in passages+versions:
  text=''.join((R/row['path']).read_text().splitlines(keepends=True)[row['start']-1:row['end']])
  check(text==row['text'] and sha(text.encode())==row['sha256'],'passage '+row.get('id',row['path']))
  if 'latest_displayed' in row:check(f"<strong>[{row['latest_displayed']}]</strong>" in text,'current version binding')
 req=read(S/'primary-requests.json');pdfs=0
 for row in req:
  if 'error' in row:continue
  p=S/'primary'/row['name'];b=p.read_bytes();check(sha(b)==row['sha256'] and len(b)==row['bytes'],'primary response '+row['name'])
  check(row['status']==200,'primary response status')
  if p.suffix=='.pdf':
   out=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True)
   check(out.returncode==row['extraction']['code']==0,'PDF extraction exit')
   check(out.stdout==p.with_suffix('.txt').read_bytes(),'PDF text replay '+p.name);pdfs+=1
 fresh=read(S/'fresh-raw-requests.json')
 for row in fresh:
  check('error' not in row and row['status']==200 and row['matches_pinned'],'fresh raw request failed')
  b=(S/row['saved']).read_bytes();check(sha(b)==row['sha256'] and b==(S/'pinned'/row['path']).read_bytes(),'fresh pin comparison')
 out=subprocess.run([sys.executable,'-B',str(E/'diagnostics.py')],cwd=R,capture_output=True,text=True)
 check(out.returncode==0,'finite diagnostics failed: '+out.stderr)
 check(json.loads(out.stdout)==read(E/'results.json'),'finite diagnostics changed')
 print(json.dumps({'status':'PASS_EVIDENCE_AND_FINITE_DIAGNOSTICS','analytic_status':'Author proved partials; principal targets G and W are gaps. Not an independent proof review.','contribution_status':'No substantial finding nominated.','sealed_artifacts':len(seal['artifacts']),'input_references':len(refs),'mutable_ledger_drift':drift,'corpus_files':len(paths),'other_tree_blobs':len(inv['other_blobs']),'pinned_files':len(pinned),'search_line_multisets':search_counts,'passages':len(passages),'capture_time_version_bindings':len(versions),'primary_http_responses':len(req),'pdf_text_replays':pdfs,'fresh_pinned_responses':len(fresh),'finite_diagnostics':'exact JSON reproduced','read_only':True},indent=2,sort_keys=True))
if __name__=='__main__':
 try:main()
 except Exception as e:
  print(json.dumps({'status':'FAIL','error':str(e)},indent=2));sys.exit(1)
