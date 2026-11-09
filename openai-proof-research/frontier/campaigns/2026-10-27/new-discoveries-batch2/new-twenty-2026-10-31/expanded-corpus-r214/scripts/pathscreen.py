import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];terms=['356542','356892','349573','351566','346262','347518','347673','348872','342385','342465','342510','342736','343879','344348','344800','402063','339824','339984','340095','340116','2210.11117','2211.08746','2102.00105','2108.03567','2004.11367','2008.02163','2008.09828','2012.00396','1904.04071','1904.07946','1904.09841','1905.06459','1909.09381','1910.14369','1912.03741','1807.05181','1808.01008','1808.04191','1808.05213','hook','Hippchen','Kasami','seaweed','Seo','Yee','Rodney','Scrimshaw','non-ambiguous','Kaplan','Hamada','EulerSymm']
out={}
for p in [D/'sources/omega-D5.json',D/'sources/omega-Problems.json',D/'sources/pool-tree.json']:
 o=json.loads(p.read_text());hits=[x['path'] for x in o['tree'] if any(t.lower() in x['path'].lower() for t in terms)];out[p.name]={'sha':o['sha'],'truncated':o.get('truncated'),'path_count':len(o['tree']),'hits':hits};print(p.name,len(o['tree']),o.get('truncated'),hits[:25])
for p in (D/'sources').glob('pool-file-*.txt'):
 hits=[]
 for n,l in enumerate(p.read_text().splitlines(),1):
  if any(t.lower() in l.lower() for t in terms):hits.append({'line':n,'text':l[:400]})
 out[p.name]=hits
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
