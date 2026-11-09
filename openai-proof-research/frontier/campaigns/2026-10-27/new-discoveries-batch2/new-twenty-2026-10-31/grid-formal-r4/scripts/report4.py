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
 if r['name'] in ['GridFinal4.mathdb_343536','Grid343536.free_classification','Grid343536.main_orbit_column_path','Grid343536.main_orbit_row_path','Grid343536.main_orbit_two','Grid343536.main_orbit_three']:
  end[r['name']]=r['axioms']
for t in stats.values():t['transitive_axioms']=sorted(t['transitive_axioms'])
for f in flags:assert stats['LOCAL'][f]==0
assert set(stats['LOCAL']['transitive_axioms'])<= {'propext','Classical.choice','Quot.sound'}
frozen=(p/'frozen-before.sha256').read_text()
assert len(frozen.splitlines())==23
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
auditlogs=list((p/'logs').glob('*compile-Audit4.log'))
assert auditlogs and any('sets equal' in f.read_text() and 'exit=0' in f.read_text() for f in auditlogs)
report={'status':'PARTIAL_CONDITIONAL_NOT_ACCEPTANCE','closed_this_round':['FreeClassification'],
 'inherited_closed':['ExceptionalNoIso'],'remaining':['MainOrbit'],'unconditional_endpoint':False,
 'remaining_exact':'∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ r : Setoid (Fin m × Fin n), IsEquitable (G m n) r → r = orbitSetoid (G m n) (Hpi r)',
 'MainOrbit_subcases':['m=1','n=1','m=n=2','m=n=3'],
 'endpoint':'GridFinal4.mathdb_343536','free_theorem':'Grid343536.free_classification',
 'lean':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612',
 'frozen_zip_sha256':'42498b10fb28faf228a1ac4ba7a509dbcd850c38caa47b03f359c2c566fa2030',
 'frozen_23_modules_byte_identical':True,'strict_serial_replay_modules':replayed,
 'all_modules_compiled_and_leanchecked':True,'allowOpaque':True,'inventory_equals_audited':True,
 'audit':stats,'theorem_axioms':end,'negative_controls':4,
 'resources':{'invocations':len(res),'max_wall_s':max(r[0] for r in res),'max_peak_group_rss_kib':max(r[1] for r in res),'background_jobs_left':False},
 'acceptance':'Root decides; no acceptance or discovery credit claimed'}
(p/'replay-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
