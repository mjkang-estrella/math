import json,gzip,re,hashlib,sqlite3,os,sys
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parent.parent;R=B.parents[3];OLD=L.parent/'sol-fresh-source-discovery-r133'
P=re.compile(rb'2610[.]22142|wild.{0,12}number|Dawkins|Nappo|Zimbizi|Tong.{0,40}spanning|Achour|degree.spread|minimum maximal matchings in permutahedra|Brenner.{0,50}Fink|2605[.]14076|quasi.regularizability',re.I)
def sha(b):return hashlib.sha256(b).hexdigest()
if sys.argv[1]=='context':
 out=[]
 for p in [B/'AGENTS.md',R/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',L.parent/'root-r131-r132-handback/DECISION.md',L.parent/'root-r133-handback/DECISION.md']:
  b=p.read_bytes();out.append(dict(path=str(p),sha256=sha(b),bytes=len(b)))
  if p.suffix=='.json':
   j=json.loads(b)
   for k,v in j.items():
    print(k, json.dumps(v)[:180] if not isinstance(v,list) else 'list length '+str(len(v)))
   if p.name=='prior-campaign-context.json':
    for k,v in j.items():
     if isinstance(v,list):
      for x in v:
       if isinstance(x,dict):print(json.dumps({a:z for a,z in x.items() if a in ['title','source_target','status','family','reason']},ensure_ascii=False))
 (L/'context-receipts.json').write_text(json.dumps(out,indent=2))
elif sys.argv[1]=='scan':
 # Reuse retained aliases to select original report roles, then discover only current
 # report paths. No rebuild of the 400k-file content/hash inventory.
 roles=re.compile(r'(?:^|/)(?:SUMMARY|discovery|PROOF|review|DECISION)[^/]*\.(?:md|txt)$',re.I)
 echoes=re.compile(r'/(?:extracted[^/]*|rebuild[^/]*|replay[^/]*|packet|inputs|evidence|history|review-core|core|source-copy|verification)/',re.I)
 paths={};aliascount=0
 with gzip.open(OLD/'history-aliases.jsonl.gz','rt') as f:
  for line in f:
   h,p=json.loads(line);aliascount+=1
   if roles.search(p) and not echoes.search(p):paths[p]=h
 inherited=len(paths)
 # Native rg inventories report filenames only, with no content aggregate.
 import subprocess
 out=subprocess.check_output(['rg','--files',str(R),'-g','*.md','-g','*.txt'],text=True)
 for s in out.splitlines():
  p=str(Path(s).relative_to(R))
  if roles.search(p) and not echoes.search(p) and not str(L.relative_to(R)) in p:paths.setdefault(p,None)
 stats=dict(alias_rows_reused=aliascount,inherited_original_paths=inherited,current_selected_paths=len(paths),read=0,unchanged=0,changed_or_new=0,missing=[],oversize=[],hits=[],retained_r111_r113=[])
 seen=set()
 for p,h in sorted(paths.items()):
  try:
   q=R/p
   if q.stat().st_size>12000000:stats['oversize'].append(p);continue
   b=q.read_bytes();hh=sha(b);stats['read']+=1
   stats['unchanged' if hh==h else 'changed_or_new']+=1
   if re.search('r11[123]/',p):stats['retained_r111_r113'].append([p,hh])
   if hh in seen:continue
   seen.add(hh)
   ms=list(P.finditer(b))
   if ms:stats['hits'].append(dict(path=p,sha256=hh,matches=[dict(offset=m.start(),text=b[max(0,m.start()-120):m.end()+220].decode(errors='replace')) for m in ms]))
  except OSError as e:stats['missing'].append([p,str(e)])
 stats.update(distinct_bodies=len(seen),pattern=P.pattern.decode(),global_cutoff=None,role_pattern=roles.pattern,echo_exclusion=echoes.pattern,limit='12MB per report; report roles only, not semantic absence; no entire lane excluded')
 (L/'history-receipt.json').write_text(json.dumps(stats,indent=2)+'\n')
 print({k:v for k,v in stats.items() if k not in ['hits','retained_r111_r113']})
 for x in stats['hits']:print(x)
