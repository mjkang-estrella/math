import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());terms=['Almkvist','Neumann','power.?dominat','restraint','Building.?Nim','Entringer','Rothe','Venn','Shigechi','balanceable','tricyclic','Hanusa','Cooper','Rowland','Abdolghafourian','octonionic']+[str(i) for i in x]+[v['source_url'].split('/')[-1] for v in x.values()];out={}
for p in (D/'sources').glob('*.json'):
 if 'tree' in p.name:
  j=json.loads(p.read_text());paths=[v['path'] for v in j.get('tree',[])];out[p.name]={'truncated':j.get('truncated'),'count':len(paths),'hits':[a for a in paths if any(re.search(t,a,re.I) for t in terms)]}
for p in (D/'sources').glob('leanpool-*'):
 if 'tree' in p.name or 'receipt' in p.name or 'head' in p.name:continue
 lines=p.read_text(errors='replace').splitlines();out[p.name]={'hits':[{'line':k,'text':a[:500]} for k,a in enumerate(lines,1) if any(re.search(t,a,re.I) for t in terms)]}
for p in (D/'sources').glob('github-search-*.json'):
 j=json.loads(p.read_text());out[p.name]={'total_count':j.get('total_count'),'hits':[(a['full_name'],a.get('description')) for a in j.get('items',[])]}
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2)[:6500])
