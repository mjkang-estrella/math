import pathlib,os,sys,subprocess,json,zipfile,hashlib,time
D=pathlib.Path(__file__).resolve().parents[1]
mods=json.loads((D/'scripts/modules.json').read_text())
archive=D/'338258-infinite-family-source.zip'
if len(sys.argv)>1:
 R=pathlib.Path(sys.argv[1]).resolve();assert R.is_relative_to(D)
else:R=D/('fresh-'+str(time.time_ns()))
R.mkdir(exist_ok=True)
with zipfile.ZipFile(archive) as z:
 for n in z.namelist():
  assert pathlib.PurePosixPath(n).name==n and n.endswith('.lean') and '\\' not in n
  assert ((z.getinfo(n).external_attr>>16)&0o170000)!=0o120000
  p=R/n;b=z.read(n)
  if p.exists():assert p.read_bytes()==b
  else:p.write_bytes(b)
env=os.environ.copy();env['REPLAY_ROOT']=str(R)
state=R/'replay-state.json'
s=json.loads(state.read_text()) if state.exists() else {'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'build':[],'check':[],'negative':{}}
assert s['archive_sha256']==hashlib.sha256(archive.read_bytes()).hexdigest()
def save():state.write_text(json.dumps(s,indent=2))
def run(args):return subprocess.call([sys.executable,'-I',str(D/'scripts/lean.py'),*args],env=env)
print('REPLAY_ROOT='+str(R),flush=True)
for m in mods:
 if m not in s['build']:
  if run(['-o',m+'.olean',m+'.lean']):sys.exit(1)
  s['build'].append(m);save()
for m in mods:
 if m not in s['check']:
  if run(['check',m]):sys.exit(1)
  s['check'].append(m);save()
for m in ['NegativePolynomial','NegativeOddSet','NegativeKernel']:
 if m not in s['negative']:
  (R/(m+'.lean')).write_bytes((D/'scripts'/(m+'.lean')).read_bytes())
  rc=run([m+'.lean']);s['negative'][m]=rc;save()
  if rc==0:raise RuntimeError('negative control accepted')
s['complete']=True;save()
(D/'latest-replay.txt').write_text(str(R)+'\n')
