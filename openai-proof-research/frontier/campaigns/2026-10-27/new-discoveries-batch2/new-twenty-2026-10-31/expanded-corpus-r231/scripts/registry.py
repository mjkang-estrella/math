import json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[1]
pat=re.compile(r'Pinnab|Loom|Dyck|Sturm|Non.?Commut|Assmus|TransitivePartition|Lattes|LengthSpectrum|LocalGirth|TwinWidth|Remoteness|SimpleOrder|Antipod|Abundan|SmallDoubl|SemiCover|MinimalBase|GallaiMilgram|SquareEnergy|IndependentSet|Constructib|Steiner|Novikov|Peakon',re.I)
out={}
for p in (D/'sources').glob('*-tree.json'):
 try:o=json.loads(p.read_text())
 except Exception as e:print(p.name,str(e));continue
 out[p.name]={'sha':o.get('sha'),'truncated':o.get('truncated'),'matches':[x for x in o.get('tree',[]) if pat.search(x['path'])]}
(D/'registry-matches.json').write_text(json.dumps(out,indent=2)+'\n')
for k,v in out.items():
 print(k,v['sha'],'truncated',v['truncated'])
 for x in v['matches']: print(x['path'])
