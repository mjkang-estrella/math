from pathlib import Path
import json,re
D=Path(__file__).resolve().parent;t=(D/'1809.07200.txt').read_text();out=[]
for r in json.loads((D/'literal-records.json').read_text()):
 if '1809.07200' not in str(r['record']['source_url']):continue
 n=r['record']['title'].split('Problem ')[-1]; hits=list(re.finditer(r'Problem\s+'+re.escape(n)+r'(?![\d.])',t));print('\nID',r['mathdb_id'],'Problem',n,'hits',len(hits))
 if hits:
  a=hits[0].start(); nxt=re.search(r'Problem\s+\d+\.\d+',t[a+20:]);end=min(a+6500,a+20+nxt.start() if nxt else len(t));s=t[a:end];print(s);out.append(dict(id=r['mathdb_id'],source='1809.07200.txt',start=a,end=end,passage=s))
for f,terms in [('1503.05295.txt',['Problem 6']),('1804.03737.txt',['Jordan','Kronecker']),('2012.02524.txt',['monomial','piecewise'])]:
 t2=(D/f).read_text();print('\nSOURCE',f,'HEADER',t2[:900])
 for term in terms:
  positions=[m.start() for m in re.finditer(re.escape(term),t2,re.I)]
  for a in positions[:5]:print(t2[max(0,a-200):a+1500])
(D/'selected-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
