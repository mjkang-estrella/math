#!/usr/bin/env python3
"""Read-only verifier. Run through verify.sh and fixed helper_guard."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r693';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def ck(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch {p}';assert h(b)==e['sha256'],f'hash mismatch {p}'
def exact(root,m):
 names={e['path'] for e in m['files']};assert len(names)==len(m['files']),'duplicate manifest path'
 assert all(not pathlib.PurePath(n).is_absolute() and '..' not in pathlib.PurePath(n).parts for n in names)
 actual={str(f.relative_to(root)) for f in root.rglob('*') if f.is_file()}
 assert actual-set(m['excluded_exact_paths'])==names,'extra/missing file'
 for e in m['files']:ck(root/e['path'],e)
def main():
 if len(sys.argv)==3 and sys.argv[1]=='--payload-only':
  root=pathlib.Path(sys.argv[2]);exact(root,j(root/'manifest.json'));return {'fixture':'PASS'}
 m=j(P/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];exact(P,m)
 for e in j(P/'flat-bindings.json'):ck(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json')
 for e in pairs:
  for k in ['original','copy']:ck(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:ck(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==8233;covered=set(map(int,cov));seen=set()
 active=j(I/'active-breadth-reservations.json');assert len(active)==3
 for r in active:
  s=set(r['ids']);assert len(s)==50 and not s&seen and not s&covered and not s&set(r['protected_ids']);seen|=s
 assert {r['lane'] for r in active}=={'claude-mathdb-primary-qualified-breadth-r628','sol-mathdb-primary-qualified-breadth-r692',P.name}
 q=j(I/'queue-r694.json');ids={r['mathdb_id'] for r in q};res=j(I/'reserved-ids-r694.json');assert len(q)==len(ids)==50 and ids==set(res['ids'])
 assert next(r['ids'] for r in active if r['lane']==P.name)==res['ids']
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 literals={x['mathdb_id']:x for x in j(P/'literal-records.json')};assert len(literals)==50
 byloc={}
 for d in ds:byloc.setdefault(d['chunk'],{})[d['line']]=d
 found=set()
 for chunk,lines in byloc.items():
  assert chunk in {e['path'] for e in chunks}
  with (C/chunk).open() as f:
   for n,line in enumerate(f,1):
    if n not in lines:continue
    r=json.loads(line);d=lines[n];ident=r['mathdb_id'];assert ident==d['mathdb_id'];found.add(ident)
    assert d['statement_utf8']==r['statement'] and d['statement_sha256']==h(r['statement'].encode())
    assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
    assert literals[ident]=={'mathdb_id':ident,'chunk':chunk,'line':n,'record':r}
    assert d['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete'] and d['classification_reason'] and d['technical_assessment'] and d['quantifier_scope']
    assert d['complete_self_contained_statement']==(d['classification']=='complete') and d['accepted_credit']==0 and d['current_registry_cleared'] is False
 assert found==ids
 ps=j(P/'proposals.json');assert isinstance(ps,list) and len(ps)<=3 and ps==[]
 for e in j(P/'source-provenance.json'):
  ident=e['mathdb_id'];ck(P/(str(ident)+'.pdf'),{'size':e['pdf_size'],'sha256':e['pdf_sha256']});ck(P/(str(ident)+'.txt'),{'size':e['text_size'],'sha256':e['text_sha256']})
 assert sum(1 for _ in (I/'routing-queue.jsonl').open())==10000
 return {'integrity':'PASS','literal_records':50,'corpus_chunks':20,'frozen_inputs':8,'direct_original_copy_pairs':len(pairs),'baseline_literal_reviews':8233,'reserved_sets':3,'proposals':0,'mathematics_or_novelty_pass':False}
if __name__=='__main__':
 try:print(json.dumps(main(),sort_keys=True))
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
