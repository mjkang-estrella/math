import pathlib,json,zipfile,hashlib,re,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
order=['Bases',*[f'Cases{k}' for k in range(8)],'Endpoint','Final','Audit']
archive=D/'lean-packet.zip'
with zipfile.ZipFile(D/'lean-packet-final.zip','x',zipfile.ZIP_DEFLATED) as z:
 for name in order:z.write(D/'lean'/f'{name}.lean',f'src/{name}.lean')
archive=D/'lean-packet-final.zip'
root=D/'replay-final';root.mkdir();(root/'build').mkdir();(root/'src').mkdir()
manifest={}
with zipfile.ZipFile(archive) as z:
 for info in z.infolist():
  assert info.filename in ['src/'+n+'.lean' for n in order]
  data=z.read(info);s=data.decode()
  assert not re.search(r'\b(sorry|admit|native_decide|ofReduceBool)\b|^\s*(axiom|unsafe|partial)\s',s,re.M)
  (root/info.filename).write_bytes(data);manifest[info.filename]=hashlib.sha256(data).hexdigest()
(D/'lean-source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
results=[]
for name in order:
 for tool in ['lean','leanchecker']:
  args=['-o',str(root/'build'/f'{name}.olean'),str(root/'src'/f'{name}.lean')] if tool=='lean' else [name]
  logname='fresh-'+tool+'-'+name
  r=subprocess.run(['python3','-I','-B',str(D/'scripts/limited.py'),logname,'bash',str(D/'scripts/replay_run.sh'),str(root/'build'),tool,*args],cwd=D)
  rec=json.loads((D/'logs'/f'{logname}.receipt.json').read_text());results.append(dict(module=name,tool=tool,**rec))
  (D/'replay-result.json').write_text(json.dumps(results,indent=2)+'\n')
  if r.returncode:sys.exit(r.returncode)
print('FRESH STRICT REPLAY AND LEANCHECKER PASS',flush=True)
