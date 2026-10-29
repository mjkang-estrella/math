exec(open(__file__.replace('source_read.py','read.py')).read().split('for f in')[0])
import re,json
for name in ['banana_v2','banana_mathdb','melonic']:
 f=p/'sources'/(name+'.html');q=P();q.feed(f.read_text());s=' '.join(q.a);f.with_suffix('.txt').write_text(s)
 print('\n',name)
 for pattern in ['Conjecture 3.9','Conjecture 3.10','solutions','Proof','Conjecture 3.1']:
  for m in list(re.finditer(pattern,s))[:2]:print(s[max(0,m.start()-70):m.start()+1400])
base=p.parent/'root-edge-irregulator-final-freeze-r1'
pat=re.compile('melonic|clasped|Banana|Gamma.*LogConcav|LinksGould|Ishii|Ultralog.*Fail|ULCFailure',re.I)
hits=[]
for name in ['omega','openai']:
 for l in (base/(name+'-tree.txt')).read_text().splitlines():
  if pat.search(l):hits.append({'registry':name,'line':l})
print('registry hits',json.dumps(hits[:80],indent=2))
d=json.loads((p/'sources/omega_delta.json').read_text());print('delta',d.get('total_commits'),[(x['filename'],x['status']) for x in d.get('files',[])])
(p/'registry-screen.json').write_text(json.dumps(dict(baseline=str(base),hits=hits,delta=[x['filename'] for x in d.get('files',[])],coverage='baseline tree paths plus live compare; bodies pending'),indent=2))
