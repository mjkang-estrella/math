import pathlib,re,json
L=pathlib.Path(__file__).resolve().parent;out=[]
for p in sorted((L/'sources').glob('*.txt')):
 lines=p.read_text().splitlines(); starts=[i for i,s in enumerate(lines) if re.match(r'^\s*(Conjecture|Question|Problem)\s+\d',s)]; chosen=set(range(min(34,len(lines))))
 for i in starts:
  chosen.update(range(max(0,i-2),min(len(lines),i+13)))
 # only numbered conjectures and header; long thesis bounded target locator
 if p.stem=='1511.02691': chosen=set(range(30))|{j for i in starts if '3.3' in lines[i] for j in range(max(0,i-3),min(len(lines),i+18))}
 entry={'source':p.stem,'ranges':[]}
 for i in sorted(chosen):entry['ranges'].append({'line':i+1,'text':lines[i]})
 out.append(entry)
(L/'located-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for e in out:
 print('\nSOURCE',e['source'])
 for r in e['ranges']:print(str(r['line'])+': '+r['text'])
