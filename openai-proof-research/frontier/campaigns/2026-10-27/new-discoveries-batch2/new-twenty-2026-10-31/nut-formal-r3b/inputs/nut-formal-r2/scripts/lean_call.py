from pathlib import Path
import os,subprocess,sys
root=Path(__file__).resolve().parents[1]
lean=Path(os.environ.get('LEAN_BIN','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'))
pk=Path(os.environ.get('LEAN_PACKAGES','/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'))
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(root/'home'),'TMPDIR':str(root/'tmp'),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','LEAN_PATH':':'.join([str(root/'formal')]+[str(p/'.lake/build/lib/lean') for p in pk.iterdir()])}
mod=sys.argv[1];args=[str(lean),'-j1','-DwarningAsError=true','-o',str(root/'formal'/(mod+'.olean')),str(root/'formal'/(mod+'.lean'))]
label=mod+'-'+str(len(list((root/'logs').glob(mod+'*.log'))))+'.log'
r=subprocess.run(['/usr/bin/python3','-I',str(root/'scripts/run_capped.py'),str(root/'logs'/label)]+args,env=env,cwd=root)
print((root/'logs'/label).read_text()[-12000:]);sys.exit(r.returncode)
