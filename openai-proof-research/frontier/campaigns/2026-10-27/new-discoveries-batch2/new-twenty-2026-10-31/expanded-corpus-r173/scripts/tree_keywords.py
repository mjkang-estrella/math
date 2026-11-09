import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];out=[]
pattern=r'overpartition|speyer|BChrom|matroidequit|matchingpreorder|heegaard|chromaticdiscrepancy|tokushige|sunflower|RainbowTree|Blanco|Zeilberger|Larman'
for p in (D/'sources').glob('*-tree.json'):
 for x in json.loads(p.read_text()).get('tree',[]):
  if re.search(pattern,x['path'],re.I):out.append({'tree':p.name,'path':x['path'],'sha':x['sha'],'type':x['type']})
(D/'outputs/tree-keyword-hits.json').write_text(json.dumps(out,indent=2));print('\n'.join(x['tree']+' '+x['path'] for x in out if x['type']=='blob')[:5000])
