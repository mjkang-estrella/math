import pathlib,json,hashlib,sys,datetime
O=pathlib.Path(__file__).resolve().parent
EX={'manifest.json','final-receipt.json'}
def require(v,msg):
 if not v: raise ValueError(msg)
def digest(p):
 b=p.read_bytes()
 return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def compare(actual,expected):
 require(actual['sha256']==expected['sha256'],'digest mismatch: '+expected['path'])
 require(actual['size']==expected['size'],'size mismatch: '+expected['path'])
def exact(actual,expected):
 require(len(expected)==len(set(expected)),'duplicate manifest path')
 require(set(actual)==set(expected),'exact file set mismatch')
def main():
 m=json.loads((O/'manifest.json').read_text())
 require(set(m['excluded_exact_paths'])==EX,'wrong exclusions')
 actual=[str(p.relative_to(O)) for p in O.rglob('*') if p.is_file() and str(p.relative_to(O)) not in EX]
 exact(actual,[r['path'] for r in m['files']])
 for r in m['files']:
  p=O/r['path'];require(not p.is_symlink(),'symlink')
  compare(digest(p),r)
 refs=json.loads((O/'flat-actual-bindings.json').read_text())
 for r in refs:
  compare(digest(pathlib.Path(r['path'])),r)
 I=O.parent/'root-mathdb-linear-two-tree-review-intake-r501'
 im=json.loads((I/'manifest.json').read_text())
 exact([str(p.relative_to(I)) for p in I.rglob('*') if p.is_file() and str(p.relative_to(I)) not in im['excluded_exact_paths']],[r['path'] for r in im['files']])
 for r in im['files']:compare(digest(I/r['path']),r)
 pairs=json.loads((I/'bindings.json').read_text())
 for r in pairs:
  for k in ('original','copy'):compare(digest(pathlib.Path(r[k])),dict(r,path=r[k]))
 # Independent rejection tests exercise the same validation functions, without modifying inputs.
 sample={'path':'self-test','sha256':'a'*64,'size':12}
 rejected=[]
 tests=[('digest',lambda:compare(dict(sample,sha256='b'*64),sample)),
        ('size',lambda:compare(dict(sample,size=13),sample)),
        ('unexpected-file',lambda:exact(['a','unexpected'],['a'])),
        ('missing-file',lambda:exact([],['a'])),
        ('duplicate-path',lambda:exact(['a'],['a','a']))]
 for name,f in tests:
  try:f()
  except ValueError:rejected.append(name)
  else:raise ValueError('negative test failed: '+name)
 receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','scientific_acceptance':False,'manifest':digest(O/'manifest.json'),'local_payloads':len(m['files']),'flat_external_bindings':len(refs),'intake_payloads':len(im['files']),'direct_pairs':len(pairs),'mismatch_rejection_tests':rejected,'upstream_verifiers_executed':False,'counts':{'additional':9,'total':39,'next':40}}
 (O/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
try:main()
except Exception as e:
 print('FAIL: '+str(e),file=sys.stderr)
 sys.exit(1)
