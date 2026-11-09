from research import *
from concurrent.futures import ThreadPoolExecutor
indices=[15,18,21,22,23,25,29,30,31,34,42,55,56,59,65,67,71,75,81]
selected=[json.loads((L/'slice.json').read_text())[i] for i in indices];(L/'selected.json').write_text(json.dumps(selected,indent=2))
texts=[];refs=[]
for d in json.loads((L/'frozen/history-bindings.json').read_text()):
 p=pathlib.Path(d['path']);before=h(p)
 if before!=d['sha256']:continue
 s=p.read_text();assert h(p)==before;refs.append(d);texts.append((str(p),s))
(L/'history-reused.json').write_text(json.dumps(refs,indent=2));hits=[]
for d in selected:
 ident=d['id'].split('/')[-1].split('v')[0]
 for p,s in texts:
  if ident in s or d['title'].lower() in s.lower():hits.append(dict(id=ident,path=p))
(L/'history-hits.json').write_text(json.dumps(hits,indent=2));print('HISTORY',hits)
def one(d):
 ident=d['id'].split('/')[-1];p=L/'sources'/(ident+'.pdf')
 if not fetch('https://arxiv.org/pdf/'+ident,p):return ident,'FAIL'
 before=h(p);t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,timeout=20);assert h(p)==before
 rec=dict(id=ident,pdf=str(p),pdf_sha256=before,text=str(t),text_sha256=h(t))
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 lines=t.read_text().splitlines();out=[]
 for i,line in enumerate(lines):
  if any(w in line.lower() for w in ['conjecture','question','problem','remains open']):out.append('\n'.join(lines[max(0,i-1):i+11]))
 (L/'sources'/(ident+'-questions.txt')).write_text('\n\n'.join(out))
 return ident,d['authors'],d['title'],'\n\n'.join(out)[-10500:]
with ThreadPoolExecutor(max_workers=4) as ex:
 for result in ex.map(one,selected):print('BODY',result)
