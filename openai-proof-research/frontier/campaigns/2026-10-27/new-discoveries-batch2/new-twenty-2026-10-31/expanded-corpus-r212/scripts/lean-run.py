import os,pathlib,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];pkg=D.parents[3]/'2026-10-14/formal/.lake/packages'
pkg=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env={**os.environ,'LEAN_PATH':':'.join(str(p) for p in pkg.glob('*/.lake/build/lib/lean')),'TMPDIR':str(D/'tmp'),'PYTHONDONTWRITEBYTECODE':'1','MALLOC_ARENA_MAX':'2'}
sys.exit(subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-j1','-M3500','-DwarningAsError=true',*sys.argv[1:]],env=env,cwd=D).returncode)
