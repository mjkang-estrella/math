import pathlib,json,re,subprocess
L=pathlib.Path(__file__).resolve().parent;C=L.parent
for p in L.glob('*-pdf.body'):
 if not p.with_suffix('.txt').exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=15)
for key in ['abm','yan','elvey']:
 lines=(L/(key+'-pdf.txt')).read_text().splitlines();out=[]
 for n,s in enumerate(lines):
  if re.search('P2|Conjecture 1.2|proof of Conjecture|conjectur|Example|Figure',s,re.I):out.append(str(n+1)+': '+' '.join(lines[max(0,n-1):n+5]))
 (L/(key+'-passages.txt')).write_text('\n'.join(out))
print((L/'yan-passages.txt').read_text()[:7000]);print((L/'abm-passages.txt').read_text()[-7500:])
# history: summarize structured entries in full ledgers already read
for p in [C/'ledger.json',C.parent/'ledger.json']:
 d=json.loads(p.read_text()); print(p.parent.name, list(d))
 for typ in ['candidates','followups']:
  for v in d.get(typ,[]):
   s=json.dumps(v,ensure_ascii=False)
   if re.search('reject|excluded|queen|positivity|graph.family|hold',s,re.I):
    print(typ, s[:650])
# root subtrees
jobs=[]
for k,r,paths in [('openai','openai/math',['preprints','lean']),('omega','the-omega-institute/trureturing',['Blueprint'])]:
 d=json.loads((L/(k+'-root.body')).read_text())
 for x in d['tree']:
  if x['path'] in paths: jobs.append((k+'-complete-'+x['path'],'https://api.github.com/repos/'+r+'/git/trees/'+x['sha']+'?recursive=1'))
(L/'complete-jobs.json').write_text(json.dumps(jobs))
