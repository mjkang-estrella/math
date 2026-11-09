import pathlib,json,hashlib,copy,datetime
L=pathlib.Path(__file__).resolve().parent
EXCLUDED={'manifest.json','final-receipt.json'}
def binding(p):
 b=p.read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def validate(m,names=None):
 assert m['excluded_exact_paths']==sorted(EXCLUDED)
 entries=m['files']; expected={e['path'] for e in entries};assert len(expected)==len(entries)
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()} if names is None else names
 assert actual-EXCLUDED==expected,'file set mismatch'
 for e in entries:
  p=L/e['path'];assert p.is_relative_to(L) and not p.is_symlink()
  assert binding(p)=={k:e[k] for k in ['sha256','size']},'payload mismatch: '+str(p)
def main():
 m=json.loads((L/'manifest.json').read_text());validate(m)
 # Actual mutation predicates are exercised without altering frozen payloads.
 negative=[]
 for key,value in [('sha256','0'*64),('size',-1)]:
  bad=copy.deepcopy(m);bad['files'][0][key]=value
  try:validate(bad)
  except AssertionError:negative.append(key)
  else:raise AssertionError('accepted corrupt '+key)
 names={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}|{'unlisted-payload'}
 try:validate(m,names)
 except AssertionError:negative.append('unexpected file')
 else:raise AssertionError('accepted extra file')
 refs=json.loads((L/'flat-original-bindings.json').read_text())['files']
 for e in refs:assert binding(pathlib.Path(e['path']))=={k:e[k] for k in ['sha256','size']},'external mismatch '+e['path']
 # Independently repeat exact intake comparison, without executing any upstream code.
 I=L.parent/'root-mathdb-three-candidate-intake-r493';im=json.loads((I/'manifest.json').read_text());expected={e['path'] for e in im['files']};assert len(expected)==len(im['files'])
 assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(im['excluded_exact_paths'])==expected
 for e in im['files']:assert binding(I/e['path'])=={k:e[k] for k in ['sha256','size']}
 d=json.loads((L/'intake-validation.json').read_text())
 for pair in d['direct_original_copy']:
  a,b=pair['copy'],pair['original'];assert binding(pathlib.Path(a['path']))==binding(pathlib.Path(b['path']))
 receipt={'integrity':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payload_count':len(m['files']),'external_flat_bindings':len(refs),'intake_payload_count':len(im['files']),'negative_tests_rejected':negative,'manifest':binding(L/'manifest.json'),'verifier':binding(pathlib.Path(__file__)),'receipt_actual_filename':'final-receipt.json','math':'See review.md; no acceptance','prior':'HOLD','substantive':'NOT CLEARED','counts':{'additional':9,'total':39,'next':40}}
 (L/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
if __name__=='__main__':main()
