import pathlib,json,re,sys
L=pathlib.Path(__file__).resolve().parent
if sys.argv[1]=='history':
 hits=json.loads((L/'history-hits.json').read_text());seen=set()
 for h in hits:
  if 'multiplier' not in h['terms'] and 'csord' not in h['terms'] and 'forg' not in h['terms']:continue
  for line in h['lines']:
   if re.search('Csord|Forg.c|1505.00355|square.root.*multiplier|multiplier.*square.root',line,re.I) and line not in seen:
    seen.add(line);print(h['path'],line)
else:
 for p in sorted((L/'retrieval').glob('2*.txt')):
  text=p.read_text();pages=text.split('\f');print('\nSOURCE',p.name)
  # definitions/introduction and explicit open statements; store indexed excerpts.
  found=[]
  for i,page in enumerate(pages):
   if i<2 or re.search(r'Conjecture [0-9]|Question [0-9]|Open problems',page):
    lines=page.splitlines();out=[]
    for j,line in enumerate(lines):
     if re.search(r'Theorem |Conjecture |Question |Definition |Proof\.',line):out.append('\n'.join(lines[max(0,j-1):j+14]))
    if out:found.append({'page':i+1,'text':'\n'.join(out)[:7000]})
  (L/(p.stem+'.excerpts.json')).write_text(json.dumps(found,indent=2))
  for x in found:print('p',x['page'],x['text'][:2500])
