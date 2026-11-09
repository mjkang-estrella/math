from pathlib import Path
import os,subprocess,json,hashlib,re
B=Path(__file__).resolve().parents[1]; F=B/'formal'
L=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
mods=['ScalarCore','SpectralCore'];names=[]
for m in mods:
 t=(F/(m+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|unsafe|native_decide)\b|^\s*axiom\b',t,re.M)
 names+=['FourProjection.'+n for n in re.findall(r'^\s*(?:lemma|theorem)\s+(\w+)',t,re.M)]
(F/'Inspect.lean').write_text('import ScalarCore\nimport SpectralCore\n'+'\n'.join('#print '+n+'\n#print axioms '+n for n in names)+'\n')
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(F)]+[str(p/'.lake/build/lib/lean') for p in P.iterdir() if (p/'.lake/build/lib/lean').is_dir()]))
results=[]
for m in mods+['Inspect']:
 cmd=[str(L),'-DwarningAsError=true','-o',str(F/(m+'.olean')),str(F/(m+'.lean'))]
 p=subprocess.run(cmd,cwd=F,env=env,text=True,capture_output=True)
 (F/(m+'.log')).write_text(p.stdout+p.stderr);results.append(dict(module=m,command=cmd,exit_code=p.returncode));assert p.returncode==0,p.stdout+p.stderr
reports=re.findall(r"'([\w.]+)' depends on axioms: \[(.*?)\]",(F/'Inspect.log').read_text(),re.S)
assert sorted(n for n,a in reports)==sorted(names)
axioms=sorted({a.strip() for n,aa in reports for a in aa.split(',')});assert set(axioms)<= {'propext','Classical.choice','Quot.sound'}
# Read revision metadata without invoking git.
git=P/'mathlib/.git'; revision_metadata={}
if git.is_dir():
 h=(git/'HEAD').read_text().strip();revision_metadata['HEAD']=h
 if h.startswith('ref: '):
  r=git/h[5:]
  if r.exists():revision_metadata['ref_value']=r.read_text().strip()
  else:revision_metadata['packed_refs']=(git/'packed-refs').read_text()
elif git.exists():revision_metadata['git_file']=git.read_text()
out=dict(status='PASS_FORMALCORE_ONLY',literal_projection_theorem=False,compiler=subprocess.check_output([str(L),'--version'],text=True).strip(),compiler_sha256=hashlib.sha256(L.read_bytes()).hexdigest(),mathlib_revision_metadata=revision_metadata,names=names,axioms=axioms,runs=results)
(B/'checks/replay.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
