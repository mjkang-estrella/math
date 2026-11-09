import os, pathlib, subprocess, sys, re
lane=pathlib.Path(__file__).resolve().parent.parent
pkg=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
roots=[pkg/'mathlib']+list(pkg.iterdir())
def source(mod):
 for root in roots:
  p=root/(mod.replace('.','/')+'.lean')
  if p.exists(): return p
 return None
def ready(mod):
 p=pathlib.Path(mod.replace('.','/')+'.olean')
 return p.exists() or any((root/'.lake/build/lib/lean'/p).exists() for root in roots)
def build(mod):
 if ready(mod): return
 p=source(mod)
 if p is None: raise RuntimeError(mod)
 data=p.read_text()
 for dep in re.findall(r'^\s*(?:public |private |meta )*import\s+([\w.]+)',data,re.M): build(dep)
 out=lane/(mod.replace('.','/')+'.olean'); out.parent.mkdir(parents=True,exist_ok=True)
 local=lane/(mod.replace('.','/')+'.lean'); local.write_text(data)
 print('BUILD',mod,flush=True)
 subprocess.run([str(lane/'scripts/run.sh'),'lean','-j1','-M3500','-o',str(out),str(local)],check=True)
for mod in sys.argv[1:]: build(mod)
