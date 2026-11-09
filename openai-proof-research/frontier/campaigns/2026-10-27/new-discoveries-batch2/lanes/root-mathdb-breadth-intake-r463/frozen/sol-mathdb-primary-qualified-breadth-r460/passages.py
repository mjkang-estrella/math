import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent; sources=json.loads((L/'sources.json').read_text())
with (L/'primary-passages.txt').open('w') as o:
 for s in sources:
  p=pathlib.Path(s['text']);lines=p.read_text().splitlines();idx=[i for i,x in enumerate(lines) if re.search(r'conjectur|open problem',x,re.I)];spans=[(0,18)]+[(max(0,i-4),min(len(lines),i+14)) for i in idx[:6]]
  o.write('\n=== '+p.stem+' ===\n');s['passage_ranges_1based']=[[a+1,b] for a,b in spans]
  for a,b in spans:
   o.write('\n'+ '\n'.join(str(i+1)+': '+lines[i] for i in range(a,b))+'\n')
  s['read_level']='selected passages prepared, reading pending; whole body and dependency audit NOT performed'
(L/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
