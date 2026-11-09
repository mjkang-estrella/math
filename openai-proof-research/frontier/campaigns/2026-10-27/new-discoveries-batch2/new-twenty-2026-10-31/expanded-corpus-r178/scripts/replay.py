import pathlib,subprocess,os,sys,json,hashlib,zipfile,tempfile
D=pathlib.Path(__file__).resolve().parents[1];P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');B=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
mode=sys.argv[1];pointer=D/'outputs/latest-replay.json'
if mode=='compile':
 R=pathlib.Path(tempfile.mkdtemp(prefix='fresh-replay-',dir=D/'tmp'))
 with zipfile.ZipFile(D/'Lean-packet.zip') as z:
  assert sorted(z.namelist())==['Audit.lean','Interpolation.lean','REPLAY.md','manifest.json'];z.extractall(R)
 assert (R/'Interpolation.lean').read_bytes()==(D/'lean/Interpolation.lean').read_bytes()
 pointer.write_text(json.dumps({'path':str(R)}))
else:
 R=pathlib.Path(json.loads(pointer.read_text())['path']) if pointer.exists() else D/'fresh-replay'
env={'PATH':str(B)+':/usr/bin:/bin','TMPDIR':str(D/'tmp'),'XDG_CACHE_HOME':str(D/'tmp'),'MALLOC_ARENA_MAX':'2','LEAN_PATH':':'.join([str(R)]+[str(p) for p in sorted(P.glob('*/.lake/build/lib/lean'))])}
if mode=='compile':cmd=[str(B/'lean'),'-M3500','-j2','-DwarningAsError=true','-o','Interpolation.olean','Interpolation.lean']
elif mode=='check':cmd=[str(B/'leanchecker'),'Interpolation']
elif mode=='audit':cmd=[str(B/'lean'),'-M3500','-j2','-DwarningAsError=true','Audit.lean']
else:raise ValueError(mode)
r=subprocess.run(cmd,cwd=R,env=env);print('source_sha256',hashlib.sha256((R/'Interpolation.lean').read_bytes()).hexdigest());sys.exit(r.returncode)
