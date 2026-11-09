exec(compile((__import__('pathlib').Path(__file__).with_name('research.py')).read_text(),'research.py','exec'))
j=[]
for name,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:j.extend([[name+'-head.json',f'https://api.github.com/repos/{repo}/commits/HEAD'],[name+'-root.json',f'https://api.github.com/repos/{repo}/git/trees/HEAD'],[name+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/HEAD?recursive=1']])
j.extend([['initial-journal.pdf','https://www.combinatorics.org/ojs/index.php/eljc/article/download/v22i2p17/pdf/'],['digital-journal.pdf','https://faculty.fairfield.edu/cstaecker/files/research/digitalhtppublished.pdf'],['spectral-later.html','https://www.sciencedirect.com/science/article/pii/S0195669823000306']])
(L/'jobs2.json').write_text(json.dumps(j))
# Record context hashes and relevant history lines. No shared writes.
import re
pat=re.compile('|'.join(map(str,ids))+r'|Hamada|Andrews.Curtis|Stahl|Kneser|antidirected|transversal|immersion|Ramsey|queen|polynomial positivity|Bordeaux|induced forest|Golomb|digital homotopy|capital.colour|concentric cylinders',re.I)
out=[];count=0
for p in B.rglob('*'):
 if L in p.parents or not p.is_file() or p.name not in ['SUMMARY.md','results.json','review.json','STATUS.md','ledger.json','prior-campaign-context.json']:continue
 b=p.read_bytes()
 if len(b)>3000000:continue
 s=b.decode('utf-8',errors='replace'); lines=s.splitlines(); matches=[(i+1,t[:6000]) for i,t in enumerate(lines) if pat.search(t)]
 if matches:out.append({'path':str(p),'sha256':h(b),'matches':matches});count+=1
for p in [B/'STATUS.md',B/'ledger.json',B.parent/'ledger.json',B.parent/'prior-campaign-context.json']:
 if p.exists(): (L/('context-'+p.parent.name+'-'+p.name)).write_bytes(p.read_bytes())
(L/'history-excerpts.json').write_text(json.dumps(out,indent=2)); print('history files',count)
