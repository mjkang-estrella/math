from pathlib import Path
import json,re,hashlib,subprocess,sys,os
lane=Path.cwd()
author=Path(json.loads(Path('ROOT-PREPARATION.json').read_text())['author_lane'])
manifest=json.loads(Path('input/author-full-manifest.json').read_text())['files']
def save(p,obj):
 subprocess.run([sys.executable,'-I','-B','write_lane.py',p],input=json.dumps(obj,indent=2)+'\n',text=True,check=True)
def inspect(logs,foreign=False):
 result=[]; union=set(); common=None; roots=None; payloads={}
 for i,p in enumerate(logs):
  raw=p.read_bytes()
  if foreign:
   rel=str(p.relative_to(author)); assert hashlib.sha256(raw).hexdigest()==manifest[rel]['sha256']
  s=raw.decode()
  decl=re.findall(r'^DECL (.*?) ORIGIN (.*?) UNSAFE (\w+)$',s,re.M)
  names={x[0] for x in decl}; assert len(names)==len(decl)==7003
  assert all(x[2]=='false' for x in decl)
  if common is None: common=set(decl)
  assert set(decl)==common
  full=re.findall(r'^FULL_DECL (.+)$',s,re.M)
  assert len(full)==len(set(full)); assert not union.intersection(full); union.update(full)
  types=len(re.findall(r'^TYPE ',s,re.M)); bodies=len(re.findall(r'^BODY ',s,re.M))
  no_body=set(re.findall(r'^NO_BODY (.+)$',s,re.M))
  assert types==len(full); assert bodies+len(set(full)&no_body)==len(full)
  assert 'ROOT_COUNT 282 CLOSURE_COUNT 7003' in s
  ax=re.search(r"ROOT_COUNT 282 CLOSURE_COUNT 7003 AXIOMS \[(.*?)\]",s).group(1)
  assert set(ax.split(", "))=={"propext","Classical.choice","Quot.sound"}
  for block in re.findall(r"^FULL_DECL .*?(?=^DECL |^ROOT_COUNT|\Z)",s,re.M|re.S):
   name=block.splitlines()[0][10:]
   payloads[name]=hashlib.sha256(block.encode()).hexdigest()
  assert s.count('⋯')==0 and s.count('…')==0
  ownroots=set(re.findall(r'^PRODUCTION_ROOT (.+)$',s,re.M))
  if ownroots:
   assert len(ownroots)==282
   if roots is None: roots=ownroots
   assert roots==ownroots
  result.append({'shard':i,'log':str(p),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'declarations':len(decl),'selected':len(full),'types':types,'bodies':bodies,'no_body_selected':len(set(full)&no_body),'abbreviations':0,'summary':re.findall(r'^ROOT_COUNT.*$',s,re.M)})
 assert union=={x[0] for x in common}
 if roots is not None: assert roots=={x[0] for x in common if "Polynexus" in x[1]}
 assert len(payloads)==7003
 return {'rendered_payload_sha256':payloads,'shards':result,'root_count':282,'closure_count':7003,'exhaustive_disjoint_body_coverage':True,'all_safe':True,'root_names':sorted(roots) if roots else None,'declaration_origins':sorted(common)}
mode=sys.argv[1]
if mode=='author':
 logs=[]
 for i in range(16):
  rec=json.loads((author/json.loads(Path('input/author-deep-audit.json').read_text())['shards'][i]['receipt']).read_text())
  rp=Path(rec['log']); assert str(rp.relative_to(author)) in manifest
  assert rec['exit']==0
  logs.append(rp)
 save('results/author-audit-inspection.json',inspect(logs,True))
else:
 logs=[next(Path('logs').glob(f'*_audit_IndependentFull{i}.log')) for i in range(16)]
 save('results/independent-audit-coverage.json',inspect(logs))
print('RECONCILED',mode,file=open(f'/proc/{os.getppid()}/fd/1','w'))
