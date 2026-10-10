"""Build owned offline replay from the readable prior design; do not run it."""
from pathlib import Path
R=Path(__file__).resolve().parents[3];E=R/'frontier/experiments/i142_uniform_algebraic_allocation';S=R/'frontier/sources/i142_uniform_algebraic_allocation';OLD=R/'frontier/experiments/i139_diffuse_weighted_positivity'
assert not(S/'seal.json').exists()
s=(OLD/'verify.py').read_text().replace('I139','I142').replace('i139_diffuse_weighted_positivity','i142_uniform_algebraic_allocation').replace('i139-diffuse-weighted-positivity','i142-uniform-algebraic-allocation').replace('(137|138)','(140|141)')
s=s.replace("mandatory='frontier/iterations/iteration136-birational-positivity-discovery-task.json'\n assert sha(read(mandatory))=='fb761d762d453a405d6ce3a740f5c6ceea3c7863c372648aeed781d82ea306cd'", "mandatory='frontier/iterations/iteration139-diffuse-weighted-positivity-task.json'\n assert sha(read(mandatory))=='4efafb184bde0e6cd5b908107e0eb29670209d4488129be0cd8b8647bda40bbc'")
s=s.replace("['required_i136_sha256']==sha(read(mandatory))","['required_i139_sha256']==sha(read(mandatory))")
s=s.replace("assert read(S+'/direct-context.txt').decode()==expected", """assert read(S+'/direct-context.txt').decode()==expected
 oldmandatory='frontier/iterations/iteration136-birational-positivity-discovery-task.json'
 assert sha(read(oldmandatory))=='fb761d762d453a405d6ce3a740f5c6ceea3c7863c372648aeed781d82ea306cd'
 oldstream='frontier/sources/i139_diffuse_weighted_positivity/direct-context.txt'
 assert read(oldstream).decode()=='\\n\\n'.join(decoded(data(oldmandatory)))+'\\n'
 for path,total in [(S+'/direct-context.txt',649),(oldstream,537),(OLD+'/context-reading.txt',4499)]:
  assert len(read(path).decode().splitlines())==total
  seen=set()
  for passage in data(S+'/read-manifest.json')['passages']:
   if passage['local']==path:seen.update(range(passage['start'],passage['end']+1))
  assert seen==set(range(1,total+1)),('new actual complete context reading coverage',path)
 """)
s=s.replace("assert actual==expected,dict(extra=sorted(actual-expected),missing=sorted(expected-actual))", """assert actual==expected,dict(extra=sorted(actual-expected),missing=sorted(expected-actual))
  prospective=json.load(sys.stdin)
  assert set(prospective)==set(owned)-{valpath}
  for path,digest in prospective.items():assert sha(read(path))==digest,('preseal owned bytes',path)
 """)
s=s.replace("[('ito',2),('roe',1),('dumnicki',1),('evans',3)]", "[('ito',2),('roe',1),('dumnicki',1),('evans',3),('biran',2),('trusiani',5),('jets2026',1)]")
(E/'verify.py').write_text(s)
for name in ['seal_once.py','validate.py']:
 s=(OLD/name).read_text().replace('i139_diffuse_weighted_positivity','i142_uniform_algebraic_allocation').replace('i139-diffuse-weighted-positivity','i142-uniform-algebraic-allocation')
 if name=='validate.py':s=s.replace('text=True,capture_output=True','text=True,capture_output=True,input=json.dumps(before)')
 (E/name).write_text(s)
p=E/'read.py';s=p.read_text();s=s.replace("base='frontier/", "assert not (S/'seal.json').exists(), 'No postseal edits'\nbase='frontier/");p.write_text(s)
print('Owned verifier, prevalidator and one-time sealer built; no inherited execution.')
