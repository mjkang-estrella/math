import sys, pathlib, importlib.util, json, subprocess, hashlib,re
sys.dont_write_bytecode=True
R=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('bounded',R/'replay-driver.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
P=m.PKG;B=R/'replay/build';S=R/'replay/extracted/src'
env={'MALLOC_ARENA_MAX':'2','PATH':str(m.LEAN.parent)+':/usr/bin:/bin','LANG':'C.UTF-8','LEAN_NUM_THREADS':'1','LEAN_PATH':':'.join([str(B),*[str(p/'.lake/build/lib/lean') for p in sorted(P.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]])}
res=[]
def run(n,cmd,gib=12):
 with (R/(n+'.stdout')).open('wb') as a,(R/(n+'.stderr')).open('wb') as b:
  p=subprocess.run(cmd,cwd=R,env=env,stdout=a,stderr=b,preexec_fn=lambda:m.caps(gib),timeout=240)
 res.append({'name':n,'command':cmd,'exit':p.returncode,'AS_GiB':gib,'CPU_seconds':180,'wall_seconds':240});return p.returncode
# All local-origin modules, rather than a hand-selected list.
t=(S/'PolynomialConvexity/Audit.lean').read_text().replace('let mods :=', 'let _mods :=').replace('set_option pp.proofs false','set_option pp.proofs true\nset_option pp.explicit true').replace('if mods.contains modName then','if modName.toString.startsWith "PolynomialConvexity." then')
(R/'ReviewAudit.lean').write_text(t)
assert run('ReviewAudit',[str(m.LEAN),'-j1','-s8192','-DElab.async=false','-DwarningAsError=true','ReviewAudit.lean'])==0
(R/'Invalid.lean').write_text('import PolynomialConvexity.Endpoint\ntheorem review_false : False := True.intro\n')
assert run('Invalid',[str(m.LEAN),'-j1','-s8192','-DElab.async=false','-DwarningAsError=true','Invalid.lean'],8)!=0
# Intentionally corrupt review-owned module, never a candidate or dependency cache object.
(B/'ReviewCorrupt.olean').write_bytes(b'NOT A LEAN MODULE\x00\xff')
assert run('Corrupt',[str(m.LEAN.parent/'leanchecker'),'-v','ReviewCorrupt'])!=0
(B/'ReviewCorrupt.olean').unlink()
run('LeanVersion',[str(m.LEAN),'--version'],8)
(R/'controls.json').write_text(json.dumps(res,indent=2))
print(json.dumps(res,indent=2))
