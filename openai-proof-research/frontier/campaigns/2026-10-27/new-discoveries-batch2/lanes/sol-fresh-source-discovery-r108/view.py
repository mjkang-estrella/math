from pathlib import Path
import re,json
L=Path(__file__).parent;s=(L/'sources/covers.raw.txt').read_text()
for term in ['Proposition 5.25','7 Open','7  Open','minor modifications','moments','7.1']:
 print('\nTERM',term)
 for m in list(re.finditer(re.escape(term),s))[-3:]:print(s[max(0,m.start()-1300):m.start()+6500])
for n in ['omega-HEAD.json','openai-HEAD.json']:
 d=json.loads((L/'sources'/n).read_text());print(n,d['sha'],d['commit']['author'],d['commit']['committer'])
