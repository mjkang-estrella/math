"""Fresh replay of every declaration; discovery acceptance is a separate review."""
import hashlib,json,os,pathlib,re,subprocess,tempfile
root=pathlib.Path(__file__).resolve().parent
lean=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
pk=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
mods=[('RootNewton','OddRootMeans'),('MomentPolynomials','OddRootMeans'),('AppellRoots','OddRootMeans'),('MeanPolynomial','OddRootMeans'),('OddMeanIdentity','OddRootMeans'),('SourceIdentity','OddRootMeans')]
(root/'build').mkdir(exist_ok=True)
run=pathlib.Path(tempfile.mkdtemp(prefix='fresh-audit-',dir=root/'build'))
inventory=[];sources=[]
for mod,ns in mods:
 source=root/'formal'/(mod+'.lean');raw=source.read_bytes();text=raw.decode()
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',text)
 names=re.findall(r'^(?:noncomputable )?(?:abbrev|def|theorem|lemma)\s+(\w+)',text,re.M)
 assert len(names)==len(set(names))
 inventory.extend(ns+'.'+n for n in names)
 (run/source.name).write_bytes(raw)
 sources.append({'path':'formal/'+source.name,'sha256':hashlib.sha256(raw).hexdigest(),'declarations':len(names)})
assert len(inventory)==len(set(inventory))
(run/'Checks.lean').write_text('\n'.join('import '+m for m,_ in mods)+'\n'+'\n'.join('#check '+n+'\n#print axioms '+n for n in inventory)+'\n')
env=dict(os.environ,LEAN_PATH=':'.join([str(run)]+[str(p/'.lake/build/lib/lean') for p in pk.iterdir() if p.is_dir()]))
version=subprocess.check_output([str(lean),'--version'],text=True).strip()
assert 'version 4.34.1,' in version
for mod in [m for m,_ in mods]+['Checks']:
 p=subprocess.run([str(lean),'-DwarningAsError=true','-o',str(run/(mod+'.olean')),str(run/(mod+'.lean'))],cwd=run,env=env,capture_output=True,text=True)
 log=p.stdout+p.stderr;(run/(mod+'.log')).write_text(log)
 if p.returncode:raise RuntimeError(log)
reports=re.findall(r"'([\w.]+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",log,re.S)
assert sorted(n for n,_ in reports)==sorted(inventory)
observed={a.strip() for _,values in reports for a in values.split(',') if a.strip()}
assert observed<={'propext','Classical.choice','Quot.sound'}
receipt={'status':'PASS','compiler':version,'modules':sources,'declarations':len(inventory),'inventory':inventory,'main_theorems':['OddRootMeans.source_conjecture_336466'],'axioms':sorted(observed),'dependency_build':str(pk),'qualification':'Fresh compiler replay of every local declaration. Dependency builds are the assigned pinned tree; no git metadata operation was performed. No novelty or collection acceptance implied.'}
(run/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
(root/'build/latest-audit.json').write_text(json.dumps(receipt|{'run_directory':str(run)},indent=2)+'\n')
print(json.dumps(receipt|{'run_directory':str(run)},indent=2))
