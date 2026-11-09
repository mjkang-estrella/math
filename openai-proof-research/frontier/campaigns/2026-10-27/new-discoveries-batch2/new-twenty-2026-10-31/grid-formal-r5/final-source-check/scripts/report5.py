from pathlib import Path
import json,hashlib,re
p=Path(__file__).resolve().parent.parent
flags=['unsafe','partial','axiom','unsafe_rec','implemented_by','extern']
stats={}
end={}
for line in (p/'audit.jsonl').open():
 r=json.loads(line)
 keys=['LOCAL' if r['local'] else 'upstream']
 if r['endpoint_import_closure']: keys.append('endpoint_import_closure')
 for k in keys:
  t=stats.setdefault(k,{'declarations':0,**{f:0 for f in flags},'transitive_axioms':set()})
  t['declarations']+=1
  for f in flags:t[f]+=int(r[f])
  t['transitive_axioms'].update(r['axioms'])
 if r['name'] in ['GridFinal5.mathdb_343536','Grid343536.free_classification','Grid343536.main_orbit_ladder','Grid343536.main_orbit_transposed_ladder','Grid343536.main_orbit_of_ordinary_border','Grid343536.main_orbit_two','Grid343536.main_orbit_three']:
  end[r['name']]=r['axioms']
for t in stats.values():t['transitive_axioms']=sorted(t['transitive_axioms'])
for f in flags:assert stats['LOCAL'][f]==0
assert set(stats['LOCAL']['transitive_axioms'])<= {'propext','Classical.choice','Quot.sound'}
frozen=(p/'frozen-before.sha256').read_text()
assert len(frozen.splitlines())==31
for row in frozen.splitlines():
 h,n=row.split()
 assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h
(p/'frozen-after.sha256').write_text(frozen)
mods=sorted(f.stem for f in (p/'src').glob('*.lean'))
replayed=[]
for m in mods:
 marker=p/'build'/(m+'.replay-ok')
 if marker.exists() and marker.read_text().strip()==hashlib.sha256((p/'src'/(m+'.lean')).read_bytes()).hexdigest():replayed.append(m)
assert mods==replayed,(mods,replayed)
res=[]
for f in (p/'logs').glob('*.log'):
 for a,b,c in re.findall(r'RESOURCE wall_s=([\d.]+) peak_rss_kib=(\d+) exit=(\d+)',f.read_text()):res.append((float(a),int(b),int(c)))
auditlogs=list((p/'logs').glob('*compile-Audit5.log'))
assert auditlogs and any('sets equal' in f.read_text() and 'exit=0' in f.read_text() for f in auditlogs)
negative_names=set()
for f in (p/'logs').glob('*-negative-*.log'):
 if 'error:' in f.read_text() and re.search(r'RESOURCE .*exit=[1-9][0-9]*',f.read_text()):
  negative_names.add(f.name.split('-negative-',1)[1])
assert len(negative_names)==4,negative_names
report={'status':'PARTIAL_CONDITIONAL_NOT_ACCEPTANCE','closed_this_round':['MainOrbit for all ladders in both orientations','ordinary positive layers','saturated border multiset rule','abstract nonbacktracking colour walks and marker timing'],
 'inherited_closed':['ExceptionalNoIso','FreeClassification'],'remaining':['OrdinaryBorderTransitivity'],'unconditional_endpoint':False,
 'remaining_exact':'∀ m n : ℕ, 3 ≤ m → 3 ≤ n → ¬ (m = 3 ∧ n = 3) → ∀ r : Setoid (Fin m × Fin n), IsEquitable (G m n) r → ∀ u v, gridLayer u = 1 → r u v → ∃ g ∈ Hpi r, g u = v',
 'MainOrbit_subcases':['m=1','n=1','m=n=2','m=n=3','m=2 and n>=3','n=2 and m>=3'],
 'endpoint':'GridFinal5.mathdb_343536','free_theorem':'Grid343536.free_classification',
 'lean':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612',
 'frozen_zip_sha256':'384a9c6a9a4e28e0e922f6545c1516216578fb8f4c73d5e469d157fddc2e378d',
 'frozen_31_modules_byte_identical':True,'strict_serial_replay_modules':replayed,
 'all_modules_compiled_and_leanchecked':True,'allowOpaque':True,'inventory_equals_audited':True,
 'audit':stats,'theorem_axioms':end,'negative_controls':4,
 'resources':{'cpus':[30,31],'invocations':len(res),'max_wall_s':max(r[0] for r in res),'max_peak_group_rss_kib':max(r[1] for r in res),'background_jobs_left':False},
 'acceptance':'Root decides; no acceptance or discovery credit claimed'}
(p/'replay-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
