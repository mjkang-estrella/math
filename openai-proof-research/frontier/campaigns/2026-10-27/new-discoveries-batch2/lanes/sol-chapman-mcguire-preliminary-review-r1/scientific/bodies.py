from retrieve import *
import re
ids=['2002.01347v1','2002.01968v2','2002.02290v3','2002.02482v2','2002.02550v1','2102.00944v2','2102.01018v2','2102.01534v2','2102.02081v1','2102.03392v1','2202.00829v1','2202.01333v2','2202.02127v1','2202.04012v1','2202.11826v2','2202.12026v1']
entries=sum([json.loads((L/(cat+'-entries.json')).read_text()) for cat in ['math.CO','math.NT','math.RA']],[])
selected=[j for j in entries if j['id'].split('/')[-1] in ids]
(L/'selected.json').write_text(json.dumps(selected,indent=2))
for ident in ids:
 p=fetch('https://arxiv.org/pdf/'+ident,ident+'.pdf')
 if not p:continue
 f=freeze(str(p.relative_to(ROOT)))
 out=L/'sources'/(ident+'.txt')
 if not out.exists():subprocess.run(['pdftotext','-layout',str(f),str(out)],check=True)
 print('\n###',ident)
 lines=out.read_text().splitlines()
 found=[]
 for i,line in enumerate(lines):
  if re.search(r'conjectur|open problem|question|problem [0-9]|future',line,re.I):
   found.append({'line':i+1,'text':'\n'.join(lines[max(0,i-2):i+15])})
 print(json.dumps(found,ensure_ascii=False)[:12500])
 (L/(ident+'-excerpts.json')).write_text(json.dumps(found,indent=2))
