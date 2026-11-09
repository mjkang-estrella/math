from pathlib import Path
import hashlib,json,re,shutil,subprocess,time,resource
p=Path(__file__).resolve().parent
mods=['Target333569','Algebra333569','Curvature333569','Cylinders333569','Diagonal333569','SeriesCurvature333569','Entropy333569','Consistency333569','TwoSided333569']
names=[]
for m in mods:
 names += ['MathDB333569.'+n for n in re.findall(r'^(?:theorem|instance|def) ([A-Za-z0-9_]+)',(p/(m+'.lean')).read_text(),re.M)]
(p/'Audit333569.lean').write_text(''.join('import '+m+'\n' for m in mods[1:])+'\n'+''.join('#print axioms '+n+'\n' for n in names))
(p/'audit-inventory.json').write_text(json.dumps(names,indent=2)+'\n')
e=p/'fresh-extracted-partial'
e.mkdir(exist_ok=True)
for m in mods+['Audit333569']:
 shutil.copyfile(p/(m+'.lean'),e/(m+'.lean'))
for f in ['replay.sh','lean-toolchain','lake-manifest.json']:shutil.copyfile(p/f,e/f)
rows=[]
for m in mods+['Audit333569']:
 started=time.monotonic()
 r=subprocess.run(['bash',str(e/'replay.sh'),'-o',m+'.olean',m+'.lean'],cwd=e,capture_output=True,text=True,timeout=200)
 (e/(m+'.log')).write_text(r.stdout+r.stderr)
 rows.append({'module':m,'exit':r.returncode,'seconds':round(time.monotonic()-started,3)})
 if r.returncode: break
allowed={'propext','Classical.choice','Quot.sound'}
audit=(e/'Audit333569.log').read_text() if (e/'Audit333569.log').exists() else ''
seen=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit,re.S)
seen += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms",audit)]
violations=[{'theorem':n,'axioms':a} for n,a in seen if set(re.findall(r'[\w.]+',a))-allowed]
r={'scope':'PARTIAL_COMPONENTS_ONLY_NOT_SOURCE_ENDPOINT','strict':True,'modules':rows,'audited_declarations':len(seen),'expected_declarations':len(names),'axiom_violations':violations,'pass':len(rows)==len(mods)+1 and all(x['exit']==0 for x in rows) and set(n for n,_ in seen)==set(names) and not violations,'external_dependency_cache_trusted':True,'dependencies_rebuilt':False,'memory_cap_lean_mb':4096,'cpu_affinity_count':2,'per_module_cpu_seconds_limit':180,'max_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
(p/'fresh-partial-replay.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
