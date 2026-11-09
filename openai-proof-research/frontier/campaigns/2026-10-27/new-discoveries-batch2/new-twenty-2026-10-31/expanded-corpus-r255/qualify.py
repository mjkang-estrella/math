import pathlib,json,re,subprocess,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent
for p in L.glob('*-pdf.body'):
 if p.read_bytes().startswith(b'%PDF') and not p.with_suffix('.txt').exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
pat=re.compile(r'(?:^|[/_-])toric|prefix.?normal|kinser|dowling|toffoli|tamari|weakly.?closed|folkman|whitham|concisen|polar|twinning|neumann.?lara|lescure|manoussakis|motzkin.?straus|homfly|knot.?floer',re.I)
jobs=[]
for p in L.glob('openai-complete-*.body'):
 d=json.loads(p.read_text()); print(p.name,'truncated',d.get('truncated'))
 for x in d.get('tree',[]):
  if pat.search(x['path']):print(p.stem,x['path'])
for p in L.glob('narrow-omega*.body'):
 print('\nBODY',p.name); print(p.read_text()[:2800])
# Exact historical ID matches, excluding raw corpus and assignment metadata.
ids=json.loads((L/'reservation.json').read_text())['ids'];pattern=r'\b(?:'+ '|'.join(map(str,ids))+r')\b'
r=subprocess.run(['rg','-n','--max-columns','1000',pattern,str(L.parent.parent),'-g','*.md','-g','results.json','-g','*ruling*.json','-g','*acceptance*.json'],capture_output=True,text=True)
lines=[s for s in r.stdout.splitlines() if str(L)+'/' not in s]
(L/'history-exact.txt').write_text('\n'.join(lines)+'\n')
print('exacthistory',len(lines))
