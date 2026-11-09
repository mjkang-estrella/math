import pathlib,os,subprocess,sys
root=pathlib.Path('/home/mj-kang/Documents/Dev/math');deps=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
env=dict(os.environ);env['LEAN_PATH']=str(pathlib.Path.cwd()/'lean')+':'+':'.join(str(p) for p in deps.glob('*/.lake/build/lib/lean'));exe=root/'dlp-research/.tools/lean-4.34.1-linux/bin/lean'
sys.exit(subprocess.call([str(exe),'-j1','-DwarningAsError=true',*sys.argv[1:]],env=env))
