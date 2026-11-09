from pathlib import Path
import re,json
D=Path(__file__).resolve().parent;out=json.loads((D/'selected-passages.json').read_text()); t=(D/'1809.07200.txt').read_text()
for n in ['5.5','5.55','7.75','9.1','9.5']:
 hits=list(re.finditer(r'Problem\s+'+re.escape(n)+r'(?![\d.])',t)); a=hits[-1].start();end=min(len(t),a+8000);nxt=re.search(r'Problem\s+\d+\.\d+',t[a+20:end]);end=a+20+nxt.start() if nxt else end
 print('\n',t[a:end]);r=next(x for x in out if x['passage'].startswith('Problem '+n+' ' ) or (x['id']==387927 and n=='7.75') or (x['id']==387715 and n=='5.55'));r.update(start=a,end=end,passage=t[a:end])
for f,terms in [('1503.05295.txt',['polynomial-like','Problem 6']),('1804.03737.txt',['Compute the Jordan','semidirect']),('2012.02524.txt',['Problem 16','Problem 17'])]:
 s=(D/f).read_text(); print('\nVERSION',re.findall(r'arXiv:\S+',s)[:3])
 for term in terms:
  for m in list(re.finditer(re.escape(term),s,re.I))[-2:]:
   a=max(0,m.start()-600);b=m.start()+3200;print(s[a:b]);out.append(dict(source=f,start=a,end=min(b,len(s)),passage=s[a:b]))
print('VERSION MAIN',re.findall(r'arXiv:\S+',t)[:3]);(D/'selected-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
