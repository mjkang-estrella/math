import pathlib,subprocess,os,sys
D=pathlib.Path(__file__).resolve().parents[1];P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'); binary='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
env={**os.environ,'LEAN_PATH':':'.join([str(D/'fresh-replay')]+[str(p) for p in sorted(P.glob('*/.lake/build/lib/lean'))]),'XDG_CACHE_HOME':str(D/'tmp')}
sys.exit(subprocess.run([binary,'-M3500','-j2','-DwarningAsError=true',*sys.argv[1:]],env=env,cwd=D).returncode)
