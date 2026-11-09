from pathlib import Path
import os,json,hashlib,zipfile,sys
D=Path(__file__).resolve().parents[1]
os.environ['PROOF_BUILD_DIR']=sys.argv[1] if len(sys.argv)>1 else 'extracted'
import run
F=run.F
F.mkdir() # Refuse to reuse a previous build directory.
zpath=D/'331705-strict-proof-source.zip'
with zipfile.ZipFile(zpath) as z:
 for i in z.infolist():
  p=Path(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and len(p.parts)==1
  assert (i.external_attr>>16)&0o170000 != 0o120000
  assert i.file_size<1000000 and (p.suffix=='.lean' or p.name=='MANIFEST.json')
  (F/p).write_bytes(z.read(i))
m=json.loads((F/'MANIFEST.json').read_text())
for n,h in m.items():assert run.sha(F/n)==h
results=[]
def check(n,args,expected=0):
 r=run.run(n,args);results.append(r)
 assert r['rc']==expected, (n,r['rc'])
for n in ['Cassinian','Wedge','Sanity']:
 check('replay-'+n,[str(run.B/'lean'),'-j1','-DwarningAsError=true','-o',n+'.olean',n+'.lean'])
for n in ['Cassinian','Wedge','Sanity']:
 check('checker-'+n,[str(run.B/'leanchecker'),n])
check('audit',[str(run.B/'lean'),'-j1','-DwarningAsError=true','Audit.lean'])
for n in ['NegativeMidpoint','NegativeStrictSlit']:
 check(n,[str(run.B/'lean'),'-j1','-DwarningAsError=true',n+'.lean'],1)
 assert 'Type mismatch' in (D/'logs'/(n+'.log')).read_text()
(D/'replay-receipt.json').write_text(json.dumps({'zip_sha256':run.sha(zpath),'fresh_directory':str(F),'passed':True,'results':results},indent=2))
