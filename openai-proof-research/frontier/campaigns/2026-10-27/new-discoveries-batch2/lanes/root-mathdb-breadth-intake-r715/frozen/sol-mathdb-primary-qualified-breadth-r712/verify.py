#!/usr/bin/env python3
"""Independent read-only verifier. Invoke through the fixed helper guard."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r711';R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size: {p}';assert digest(b)==e['sha256'],f'hash: {p}'
def payload(root):
 m=load(root/'manifest.json');exc=m.get('excluded_exact_paths',[]);assert set(exc)=={'manifest.json','final-verification-receipt.json'}
 files=m['files'];names=[e['path'] for e in files];assert len(names)==len(set(names));assert not set(names)&set(exc)
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};assert actual==set(names)|(set(exc)&actual),'extra/missing payload'
 for e in files:check(root/e['path'],e)
def main():
 if len(sys.argv)>1:
  assert len(sys.argv)==3 and sys.argv[1]=='--payload-only';payload(pathlib.Path(sys.argv[2]));return {'payload':'PASS'}
 payload(P)
 for e in load(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 im=load(I/'manifest.json');actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()};assert actual=={e['path'] for e in im['files']}|set(im['excluded_exact_paths'])
 for e in im['files']:check(I/e['path'],e)
 pairs=load(I/'bindings.json')
 for e in pairs:
  check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
 assert (R/'manifest.json').read_bytes()==(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes()
 inv=load(R/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:check(R/e['path'],e)
 q=load(I/'queue-r712.json');res=load(I/'reserved-ids-r712.json');ids=set(res['ids']);assert len(ids)==len(q)==50 and ids=={e['mathdb_id'] for e in q}
 coverage=set(map(int,load(I/'coverage-delta.json')));assert len(coverage)==8683
 seen=set();active=load(I/'active-breadth-reservations.json');assert len(active)==3
 for a in active:
  s=set(a['ids']);assert len(s)==50 and not s&seen and not s&coverage and not s&set(a['protected_ids']);seen|=s
 assert any(set(a['ids'])==ids and a['lane']==P.name for a in active)
 literal=load(P/'literal-records.json');disps=load(P/'dispositions.json');assert len(literal)==len(disps)==50
 assert len({d['record']['mathdb_id'] for d in literal})==50
 assert {d['record']['mathdb_id'] for d in literal}==ids=={d['mathdb_id'] for d in disps}
 found={}
 for e in chunks:
  path=R/e['path']
  with path.open() as f:
   for n,line in enumerate(f,1):
    r=json.loads(line)
    if r['mathdb_id'] in ids:
     assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(path),n,r)
 assert len(found)==50
 ds={d['mathdb_id']:d for d in disps}
 for e in literal:
  i=e['record']['mathdb_id'];c,n,r=found[i];d=ds[i]
  assert e['chunk']==d['corpus_chunk']==c and e['line']==d['corpus_line']==n and e['record']==r
  h=digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert h==e['canonical_record_sha256']==d['canonical_record_sha256']
  assert r['statement']==d['exact_utf8_statement'];assert digest(r['statement'].encode())==d['statement_utf8_sha256']
  assert d['classification'] in {'complete','definition-dependent','scope-ambiguous','incomplete'}
  assert d['classification_reason'] and d['quantifiers'] and d['technical_assessment'];assert d['accepted_credit']==0
 assert load(P/'proposals.json')==[]
 for fname in ['source-provenance.json','successor-provenance.json']:
  for e in load(P/fname):
   if 'path' in e:check(P/e['path'],e)
   for k in ['pdf','text']:
    if k in e:check(P/e[k],{'sha256':e[k+'_sha256'],'size':e[k+'_size']})
 return {'integrity':'PASS','assigned_literals':50,'baseline':8683,'chunks':20,'frozen_inputs':8,'direct_pairs':len(pairs),'disjoint_reservations':3,'proposals':0,'mathematics':'NOT_CERTIFIED','novelty':'HOLD'}
if __name__=='__main__':
 try:print(json.dumps(main(),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
