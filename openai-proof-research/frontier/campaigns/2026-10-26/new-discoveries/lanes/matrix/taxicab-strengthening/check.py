import os,subprocess,pathlib,sys
root=pathlib.Path(__file__).resolve().parent;pk=root.parents[5]/'2026-10-14/formal/.lake/packages'
# The package tree is the assigned immutable dependency build.
pk=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
build=root/'build';build.mkdir(exist_ok=True);env=dict(os.environ,LEAN_PATH=':'.join([str(build)]+[str(p/'.lake/build/lib/lean') for p in pk.iterdir() if p.is_dir()]))
mod=sys.argv[1] if len(sys.argv)>1 else 'StrengthenedScalar';source=root/'formal'/f'{mod}.lean';(build/source.name).write_bytes(source.read_bytes());r=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-DwarningAsError=true','-o',str(build/f'{mod}.olean'),str(build/source.name)],env=env,cwd=build,capture_output=True,text=True);(build/f'{mod}.log').write_text(r.stdout+r.stderr);print(r.stdout+r.stderr);raise SystemExit(r.returncode)
