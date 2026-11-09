from pathlib import Path
import os,json,hashlib,zipfile,sys
D=Path(__file__).resolve().parents[1]
build=sys.argv[1] if len(sys.argv)>1 else 'extracted'
assert len(Path(build).parts)==1 and build not in ('.','..') and not Path(build).is_absolute()
os.environ['PROOF_BUILD_DIR']=build
import run
F=run.F
assert not list(D.glob('*.olean')) and not list((D/'formal').glob('*.olean')), 'Existing source oleans refused'
pins=json.loads((D/'pins.json').read_text())
assert run.sha(run.B/'lean')==pins['compiler_sha256']
assert run.sha(run.B/'leanchecker')==pins['checker_sha256']
assert run.sha(D/'lake-manifest.json')==pins['dependency_manifest_sha256']
F.mkdir() # Refuse to reuse a previous build directory.
(D/'logs').mkdir(exist_ok=True)
zpath=Path(os.environ.get('SOURCE_ZIP',str(D/'331705-proof-source.zip'))).resolve()
with zipfile.ZipFile(zpath) as z:
 infos=z.infolist()
 assert len(infos)<200 and len({i.filename for i in infos})==len(infos)
 for i in infos:
  p=Path(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename
  assert (i.external_attr>>16)&0o170000 != 0o120000
  assert i.file_size<1000000 and p.suffix not in ['.olean','.ilean']
  target=F/p;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(i))
m=json.loads((F/'MANIFEST.json').read_text())
assert set(m)=={i.filename for i in infos}-{'MANIFEST.json'}
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
