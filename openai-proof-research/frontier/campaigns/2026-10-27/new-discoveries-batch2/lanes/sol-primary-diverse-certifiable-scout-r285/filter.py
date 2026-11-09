from research import *
R=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
P=R/'frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing'
terms=re.compile(r'snake.polynomial|nikolov|crumby|list.packing|extended.petersen|rainbow.connect|poorly.matchable|type.A.order|type.B.order|dual.critical|reflection.{0,30}(rational|growth)|fullerene|linton|annulus|shadows.of.polynomials|2312.09482|linear.complementary.pair',re.I)
rows=[];bindings=[]
for p in list((P/'Problems').glob('*.md'))+list((P/'D5').rglob('*.lean')):
 if p.stat().st_size>2000000:continue
 d=p.read_bytes();h=sha(d);bindings.append(dict(original=str(p),sha256=h,bytes=len(d)))
 s=d.decode(errors='replace');ms=list(terms.finditer(s))
 if ms:rows.append(dict(path=str(p),sha256=h,hits=[s[max(0,m.start()-120):m.end()+220] for m in ms[:8]]))
 assert sha(p.read_bytes())==h
(L/'duplicate-filter-bindings.json').write_text(json.dumps(bindings,indent=2))
(L/'semantic-hits.json').write_text(json.dumps(rows,indent=2));print('files',len(bindings),'hits',len(rows))
for r in rows: print(r['path'],r['hits'][:3])
