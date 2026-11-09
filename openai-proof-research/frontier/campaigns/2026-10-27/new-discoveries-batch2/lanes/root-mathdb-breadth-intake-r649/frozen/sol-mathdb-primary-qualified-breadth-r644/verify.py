"""Read-only independent integrity verifier. Run through verify.sh. No upstream code executed."""
import pathlib,json,hashlib,sys,argparse
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r643';R=L/'pi-mathdb-full-corpus-inventory-r301'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def check(p,x):
 b=p.read_bytes();assert len(b)==x.get('size',x.get('bytes')),('size',str(p));assert sha(b)==x['sha256'],('hash',str(p))
def payload(root,m,fault=None):
 assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 expected={x['path'] for x in m['files']};assert len(expected)==len(m['files'])
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 if fault=='extra':actual.add('synthetic-extra-file')
 assert expected==actual,('exact payload',expected^actual)
 for i,x in enumerate(m['files']):
  b=(root/x['path']).read_bytes()
  if i==0 and fault=='size':b+=b'!'
  if i==0 and fault=='hash':b=bytes([b[0]^1])+b[1:]
  assert len(b)==x['size'],('payload size',x['path'])
  assert sha(b)==x['sha256'],('payload hash',x['path'])
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--fault',choices=['hash','size','extra']);args=ap.parse_args()
 payload(P,load(P/'manifest.json'),args.fault)
 check(I/'manifest.json',dict(size=19288,sha256='b6da03bcc5fe26301219dcc65cc4072b25f4592356bcb142f3bed681ecc19447'))
 im=load(I/'manifest.json');expected={x['path'] for x in im['files']};actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(im['excluded_exact_paths']);assert actual==expected
 for x in im['files']:check(I/x['path'],x)
 for x in load(I/'bindings.json'):
  check(pathlib.Path(x['original']),x);check(pathlib.Path(x['copy']),x);assert pathlib.Path(x['original']).read_bytes()==pathlib.Path(x['copy']).read_bytes()
 for x in load(P/'flat-bindings.json'):check(pathlib.Path(x['path']),x)
 check(R/'manifest.json',next(x for x in im['files'] if x['path']=='frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'))
 rm=load(R/'manifest.json');chunks=[x for x in rm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for x in chunks+rm['frozen_inputs']:check(R/x['path'],x)
 coverage=set(map(int,load(I/'coverage-delta.json')));assert len(coverage)==7033
 reservations=load(I/'active-breadth-reservations.json');assert len(reservations)==3;seen=set()
 for r in reservations:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&coverage and not ids&set(r['protected_ids']);seen|=ids
 ids=set(load(I/'reserved-ids-r644.json')['ids']);assert ids=={x['mathdb_id'] for x in load(I/'queue-r644.json')}
 d=load(P/'dispositions.json');lits=load(P/'literal-records.json');assert len(d)==len(lits)==50 and {x['mathdb_id'] for x in d}==ids
 found={}
 for ch in chunks:
  p=R/ch['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line);id=r.get('mathdb_id',r.get('id'))
   if id in ids:assert id not in found;found[id]=(r,str(p),n)
 assert set(found)==ids
 for x in lits:
  r=x['record'];id=r['mathdb_id'];original,p,n=found[id];assert r==original and x['chunk']==p and x['line']==n
  canon=sha(json.dumps(original,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert x['canonical_record_sha256']==canon
  z=next(t for t in d if t['mathdb_id']==id);assert z['statement']==original['statement'] and z['canonical_record_sha256']==canon and z['statement_utf8_sha256']==sha(original['statement'].encode()) and z['corpus_line']==n and z['corpus_chunk']==p
  assert z['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete'] and z['classification_reason'] and z['quantifier_scope'] and z['technical_disposition'] and z['accepted_credit']==0
 assert len(load(P/'proposals.json'))<=3
 for x in load(P/'source-provenance.json'):
  if 'path' in x:check(P/x['path'],x)
 for x in load(P/'selected-passages.json'):
  lines=(P/x['source']).read_text().splitlines();assert x['text']=='\n'.join(lines[x['start_line']-1:x['end_line']])
 print(json.dumps(dict(integrity='PASS',literal_records=50,baseline=7033,original_chunks=20,frozen_inputs=8,reservation_sets=3,proposals=len(load(P/'proposals.json')),math_novelty='NOT_CERTIFIED')))
if __name__=='__main__':
 try:main()
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
