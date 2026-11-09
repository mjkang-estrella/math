from pathlib import Path
import json,hashlib,re
p=Path(__file__).resolve().parent.parent
flags=['unsafe','partial','axiom','unsafe_rec','implemented_by','extern']
stats={}; endpoints={}
for line in (p/'audit.jsonl').open():
 r=json.loads(line)
 keys=['LOCAL' if r['local'] else 'upstream']
 if r['endpoint_import_closure']: keys.append('endpoint_import_closure')
 for k in keys:
  t=stats.setdefault(k,{'declarations':0,**{f:0 for f in flags},'transitive_axioms':set()})
  t['declarations']+=1
  for f in flags:t[f]+=int(r[f])
  t['transitive_axioms'].update(r['axioms'])
 if r['name'] in ['GridFinal6.mathdb_343536','Grid343536.ordinary_border_transitivity','Grid343536.main_orbit_proved','Grid343536.ordinary_corner_transitivity','Grid343536.ordinary_internal_border_transitivity']:
  endpoints[r['name']]=r['axioms']
for t in stats.values():t['transitive_axioms']=sorted(t['transitive_axioms'])
for f in flags:assert stats['LOCAL'][f]==0
assert set(stats['LOCAL']['transitive_axioms']) <= {'propext','Classical.choice','Quot.sound'}
assert len(endpoints)==5
frozen=(p/'frozen-before.sha256').read_text()
assert len(frozen.splitlines())==38
for row in frozen.splitlines():
 h,n=row.split();assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h
assert (p/'frozen-after.sha256').read_text()==frozen
mods=sorted(f.stem for f in (p/'src').glob('*.lean'))
for m in mods:
 assert (p/'build'/(m+'.replay-ok')).read_text().strip()==hashlib.sha256((p/'src'/(m+'.lean')).read_bytes()).hexdigest(),m
assert len(mods)==47
alog=list((p/'logs').glob('*compile-Audit6.log'))
assert any('sets equal' in f.read_text() and 'exit=0' in f.read_text() for f in alog)
neg=set()
resources=[]
for f in (p/'logs').glob('*.log'):
 s=f.read_text()
 resources.extend((float(a),int(b),int(c)) for a,b,c in re.findall(r'RESOURCE wall_s=([\d.]+) peak_rss_kib=(\d+) exit=(\d+)',s))
 if '-negative-' in f.name and 'error:' in s and re.search(r'RESOURCE .*exit=[1-9]',s):neg.add(f.name.split('-negative-',1)[1])
assert len(neg)==4
report={'status':'CLOSED_IMPLEMENTATION_NOT_ACCEPTANCE','endpoint':'GridFinal6.mathdb_343536','unconditional_endpoint':True,'remaining':[],
'closed_this_round':['ordinary_border_transitivity : OrdinaryBorderTransitivity','main_orbit_proved : MainOrbit','GridFinal6.mathdb_343536 (unconditional)','ordinary_corner_transitivity','ordinary_internal_border_transitivity'],
'lean':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','frozen_zip_sha256':'2ea9a4d731a026da9f564eb05f11254144b4874cae7fba57ba678ca23cfddd46',
'frozen_38_modules_byte_identical':True,'strict_serial_replay_modules':mods,'all_modules_compiled_and_leanchecked':True,'allowOpaque':True,'inventory_equals_audited':True,
'audit':stats,'theorem_axioms':endpoints,'negative_controls':sorted(neg),'resources':{'cpus':[30,31],'max_wall_s':max(x[0] for x in resources),'max_peak_group_rss_kib':max(x[1] for x in resources),'background_jobs_left':False},
'resource_deviation':'Development audit briefly overlapped fresh replay; terminated and excluded. See RESOURCE-NOTE.md.','acceptance':'Root decides; no self-acceptance or credit claimed.'}
(p/'replay-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
