from pathlib import Path
import json,datetime,os
D=Path(__file__).resolve().parents[1]
coverage={}
for mode in ['domatic','fork','ideal']:
 rows=[]
 for p in sorted((D/'outputs').glob('graph8-'+mode+'*.json')):rows+=json.loads(p.read_text())
 ids=[r[0] for r in rows];assert len(ids)==len(set(ids))==12346 and set(ids)==set(range(12346))
 if mode=='domatic':assert not any(v and abs(v[0]-v[1])>1 for _,v in rows)
 if mode=='fork':assert not any(v not in [None,True] for _,v in rows)
 if mode=='ideal':assert not any(v and v[0]>v[1] for _,v in rows)
 coverage[mode]={'dataset_entries':12346,'covered_without_overlap':12346,'witnesses':0}
ars=[]
for p in (D/'outputs').glob('arbor-7-*.json'):ars+=json.loads(p.read_text())
assert len(ars)==332 and {a['index'] for a in ars}==set(range(332))
assert all(a['hstar']==a['word'] for a in ars)
coverage['arbor7']={'all_shapes':332,'checked':332,'disagreements':0}
(D/'receipts/final-coverage-validation.json').write_text(json.dumps(coverage,indent=2)+'\n')
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  if p.joinpath('cwd').resolve()!=D:continue
  cmd=p.joinpath('cmdline').read_bytes().split(b'\0');args=[x.decode(errors='replace') for x in cmd if x]
  if any(a.startswith('scripts/') or a.startswith(str(D/'scripts')+'/') for a in args):active.append({'pid':int(p.name),'argv':args})
 except (OSError,PermissionError):pass
assert not active,active
(D/'receipts/no-background-jobs.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Processes with lane cwd and a lane script argument, plus completed tool-session receipts','active_lane_script_processes':active},indent=2)+'\n')
p=D/'SUMMARY.md';s=p.read_text().replace('Arbor calculations compare exact Ehrhart coefficients with complete word enumeration; direct and subtree-convolution methods agree at overlapping orders.','Arbor calculations compare exact Ehrhart coefficients with complete word enumeration through size 7, including all 332 shapes at that size; direct and subtree-convolution methods agree at overlapping orders.');p.write_text(s)
print(json.dumps(coverage));print('No active lane script processes.')
