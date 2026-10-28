from pathlib import Path
import hashlib,json,re,subprocess,shutil,tempfile
p=Path(__file__).resolve().parent
mods=['EulerMoments','SeriesConvergence','SourceDefs','RealAnalytic','NormBridge','Approximation']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins=json.loads((p/'pins.json').read_text())
assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
assert subprocess.check_output([pins['lean_binary'],'--version'],text=True).strip()==pins['lean_version']
for n,v in pins['packages'].items():assert subprocess.check_output(['git','-C',v['path'],'rev-parse','HEAD'],text=True).strip()==v['revision'],n
names=[]
for m in mods:
    source=(p/'formal'/(m+'.lean')).read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',source),m
    names+=re.findall(r"^(?:noncomputable )?(?:def|theorem|lemma) ([\w']+)",source,re.M)
assert len(names)==len(set(names))==37
out=p/'verification';out.mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='mittag-components-fresh-') as tmp:
    t=Path(tmp)
    for n in [*(m+'.lean' for m in mods),'Checks.lean','run_lean.py']:shutil.copy2(p/'formal'/n,t/n)
    for m in mods:
        r=subprocess.run(['python3','run_lean.py','-DwarningAsError=true','-o',m+'.olean',m+'.lean'],cwd=t,capture_output=True,text=True)
        (out/(m+'.log')).write_text(r.stdout+r.stderr);assert r.returncode==0 and not r.stdout and not r.stderr,(m,r.returncode,r.stdout,r.stderr)
    r=subprocess.run(['python3','run_lean.py','-DwarningAsError=true','Checks.lean'],cwd=t,capture_output=True,text=True)
    (out/'Checks.log').write_text(r.stdout+r.stderr);assert r.returncode==0 and not r.stderr
    reports=re.findall(r"^'(.+)' depends on axioms: \[([^]]*)\]",r.stdout,re.M)
    assert {n for n,_ in reports}=={'MittagModulus.'+n for n in names}
    allowed={'propext','Classical.choice','Quot.sound'}
    for n,axs in reports:assert set(filter(None,axs.split(', ')))<=allowed,(n,axs)
    audit={'status':'PASS supporting genuine series/Gamma approximation components ONLY','scope':'No proof of SourceClaim370772 or complete monotonicity; positive angular kernel and integral-operator representation remain','modules':len(mods),'declarations':len(names),'fresh_source_copy':True,'warnings_as_errors':True,'no_local_oleans':True,'allowed_axioms':sorted(allowed),'source_hashes':{m+'.lean':sha(p/'formal'/(m+'.lean')) for m in mods},'pins_sha256':sha(p/'pins.json'),'checks_sha256':sha(out/'Checks.log')}
    (out/'audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print('PASS6 supporting modules/37 declarations; actual series and Gamma limits; full source CM endpoint absent')
