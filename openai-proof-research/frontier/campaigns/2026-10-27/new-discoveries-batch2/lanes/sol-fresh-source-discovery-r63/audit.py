import pathlib,json,hashlib,re
P=pathlib.Path(__file__).resolve().parent; B=P.parent.parent
paths=[B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',B/'AGENTS.md',B.parents[3]/'AGENTS.md']
paths+= [B/'lanes'/s/'SUMMARY.md' for s in ['sol-fresh-source-discovery-r59','sol-fresh-source-discovery-r60']]
paths += [B/'lanes/sol-fresh-source-discovery-r57/sources'/s for s in ['omega-D5.json','omega-Problems.json','omega-blueprint.json']]
paths += [B/'lanes/sol-fresh-probability-finite-r21/sources/omega-D5-tree.json']
report=[]
for p in paths:
 if not p.exists():continue
 data=p.read_bytes();row={'path':str(p),'sha256':hashlib.sha256(data).hexdigest()}
 if p.suffix=='.json':
  j=json.loads(data)
  if 'tree' in j:
   row.update(entries=len(j['tree']),truncated=j.get('truncated'),matches=[x['path'] for x in j['tree'] if re.search('guday|gueday|sahin|agoh|conditional|ratsaby',x['path'],re.I)])
 report.append(row)
(P/'context-registry-screen.json').write_text(json.dumps(report,indent=2)); print(json.dumps(report,indent=2))
