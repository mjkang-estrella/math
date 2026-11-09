import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent
for o in json.loads((L/'registry-screen.json').read_text()):
 if o.get('matches'):print(o['path'],json.dumps(o['matches'],indent=1)[:13000])
for name in ['aluffi-refutation','gessel-proof','lobb-grant']:
 p=L/'sources'/f'{name}.txt';s=p.read_text().splitlines();print('\nSOURCE',name)
 for i,l in enumerate(s):
  if re.search(r'Theorem 1\.|Conjecture|even.degree|odd.degree|counterexample|conjecture.*proved',l,re.I):print(i+1,'\n'.join(s[max(0,i-1):i+6]))
