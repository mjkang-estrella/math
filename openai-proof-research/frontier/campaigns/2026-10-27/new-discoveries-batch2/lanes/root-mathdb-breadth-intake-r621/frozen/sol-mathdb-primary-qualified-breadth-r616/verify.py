#!/usr/bin/env python3
"""Independent read-only verifier. Run under the fixed helper_guard.py. --fault exercises in-memory rejection only."""
import pathlib,json,hashlib,sys,argparse
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r615';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text(encoding='utf-8'))
def digest(b):return hashlib.sha256(b).hexdigest()
def entry(p):
 b=p.read_bytes();return {'sha256':digest(b),'size':len(b)}
def check(p,e):
 assert not p.is_symlink(),f'symlink: {p}'
 assert entry(p)=={'sha256':e['sha256'],'size':e.get('size',e.get('bytes'))},f'hash/size mismatch: {p}'
def exact(root,m,fault=None):
 assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'] if root==P else True
 names={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};expected={e['path'] for e in m['files']}
 assert len(expected)==len(m['files'])
 if fault=='extra':names.add('injected-extra-file')
 assert names-set(m['excluded_exact_paths'])==expected,'extra/missing file rejection'
 for n,e in enumerate(m['files']):
  if fault and n==0:
   e=dict(e)
   if fault=='hash':e['sha256']='0'*64
   if fault=='size':e['size']=e.get('size',e.get('bytes'))+1
  check(root/e['path'],e)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--fault',choices=['hash','size','extra']);a=ap.parse_args()
 exact(P,j(P/'manifest.json'),a.fault)
 check(I/'manifest.json',{'sha256':'d3ded06c6a20fe4acefd4c63a1835a25c891707605d1c8e8a3d79c6a43f209fe','size':10492});exact(I,j(I/'manifest.json'))
 flat=j(P/'flat-bindings.json')
 for path,e in flat.items():check(pathlib.Path(path),e)
 for e in j(I/'bindings.json'):
  for key in ['original','copy']:check(pathlib.Path(e[key]),e)
 invcopy=I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json';check(C/'manifest.json',entry(invcopy));cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 queue=j(I/'queue-r616.json');reserved=j(I/'reserved-ids-r616.json');ids={e['mathdb_id'] for e in queue};cov=j(I/'coverage-delta.json');covered={int(x) for x in cov};assert len(covered)==6333
 assert len(queue)==50 and len(ids)==50 and ids==set(reserved['ids']);assert reserved['lane']==P.name and reserved['coverage_baseline']==6333
 active=j(I/'active-breadth-reservations.json');seen=set();assert len(active)==3
 for e in active:
  s=set(e['ids']);assert len(s)==50 and not s&seen and not s&covered and not s&set(e['protected_ids']);seen|=s
 assert ids<=seen and not ids&set(reserved['protected_ids'])
 rows=j(P/'literal-records.json');ds=j(P/'dispositions.json');assert len(rows)==len(ds)==50 and {e['mathdb_id'] for e in ds}==ids and len(j(P/'proposals.json'))<=3
 byid={e['mathdb_id']:e for e in ds};locations={}
 for e in rows:
  assert pathlib.Path(e['chunk']).parent==C/'corpus';locations.setdefault(e['chunk'],{})[e['line']]=e
 count=0
 for path,locs in locations.items():
  with open(path,encoding='utf-8') as f:
   for n,line in enumerate(f,1):
    if n not in locs:continue
    e=locs[n];r=json.loads(line);assert r==e['record'];i=r['mathdb_id'];assert i in ids
    canonical=digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'));st=digest(r['statement'].encode('utf-8'));d=byid[i]
    assert canonical==e['canonical_record_sha256']==d['canonical_record_sha256'] and st==e['statement_utf8_sha256']==d['statement_utf8_sha256'];assert d['statement']==r['statement'] and d['line']==n and d['chunk']==path
    assert d['literal_record_reviewed'] and d['quantifier_summary'] and d['technical_disposition']
    assert d['complete_mathematical_statement_coverage']==(d['scope_flag']=='complete')
    assert d['accepted_credit']==0 and not d['promotion'] and not d['prior_cleared'];count+=1
 assert count==50
 for e in j(P/'source-provenance.json'):check(pathlib.Path(e['path']),e)
 for e in j(P/'derivative-bindings.json'):check(pathlib.Path(e['path']),e)
 sc=j(P/'source-coverage.json');assert sc['complete_mathematical_statement_coverage']==sum(e['complete_mathematical_statement_coverage'] for e in ds)
 result={'integrity':'PASS','intake_exact_payload':True,'flat_original_files_checked':len(flat),'direct_pairs':len(j(I/'bindings.json')),'original_chunks':20,'frozen_inputs':8,'active_disjoint_sets':3,'baseline_reviews':6333,'literal_records':50,'complete_mathematical_statement_coverage':sc['complete_mathematical_statement_coverage'],'proposals':len(j(P/'proposals.json')),'mathematical_pass':False,'novelty_pass':False}
 print(json.dumps(result,sort_keys=True))
if __name__=='__main__':
 try:main()
 except Exception as ex:print('FAIL: '+str(ex),file=sys.stderr);sys.exit(1)
