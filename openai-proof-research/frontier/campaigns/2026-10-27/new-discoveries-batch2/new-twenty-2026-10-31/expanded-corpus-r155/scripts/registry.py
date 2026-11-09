import json,pathlib,re
L=pathlib.Path(__file__).resolve().parents[1]
r=json.loads((L/'sources/omega-tree.json').read_text());print('truncated',r.get('truncated'),'paths',len(r.get('tree',[])))
pat=re.compile('gray|descent|tableau|coprime|hypertope|lascoux|grothendieck|stanley|ramsey|rotation|bent|pratt|harer|kolberg|kneser|transitive|binomial',re.I)
for x in r.get('tree',[]):
 if pat.search(x['path']):print(x['path'])
for n in [5,7,9,11]:
 r=json.loads((L/f'outputs/flower{n}.json').read_text());print('flower',n,'nodes',r['search_nodes'],'complete',r['complete_flows_examined'],'witness',r['answer'] is not None)
for i in ['325786','341682','341975','342507','337584']:
 s=(L/f'sources/{i}.abs').read_text();hist=s[s.find('Submission history'):s.find('Submission history')+1800];print(i,re.sub('<[^>]+>',' ',hist))
