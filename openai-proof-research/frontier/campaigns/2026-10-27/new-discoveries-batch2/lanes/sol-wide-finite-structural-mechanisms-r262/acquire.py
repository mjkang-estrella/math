from explore import *
from concurrent.futures import ThreadPoolExecutor
indices=[2,7,8,15,19,24,27,28,34,36,40,43,51,56,64,70,72,88,91,92,94,99]
selected=[json.loads((L/'slice.json').read_text())[i] for i in indices]
(L/'selected.json').write_text(json.dumps(selected,indent=2))
refs=[];texts=[]
for p in sorted((B/'lanes').glob('*/SCOUTING.md'))+sorted((B/'lanes').glob('*/SUMMARY.md')):
 if p.parent==L:continue
 before=digest(p);s=p.read_text();assert before==digest(p)
 refs.append(dict(path=str(p),sha256=before));texts.append((str(p),s))
(L/'history-bindings.json').write_text(json.dumps(refs,indent=2))
hits=[]
for d in selected:
 ident=d['id'].split('/')[-1].split('v')[0]
 for p,s in texts:
  if ident in s or d['title'].lower() in s.lower():hits.append(dict(id=ident,path=p))
(L/'history-hits.json').write_text(json.dumps(hits,indent=2));print('HISTORY',hits)
def one(d):
 ident=d['id'].split('/')[-1];p=L/'sources'/(ident+'.pdf');p.parent.mkdir(exist_ok=True)
 if not fetch('https://arxiv.org/pdf/'+ident,p):return
 before=digest(p);t=p.with_suffix('.txt')
 subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,timeout=25)
 assert before==digest(p)
 rec=dict(id=ident,pdf=str(p),pdf_sha256=before,text=str(t),text_sha256=digest(t))
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 s=t.read_text();lines=s.splitlines();out=[]
 for i,line in enumerate(lines):
  if any(w in line.lower() for w in ['conjecture','question','problem','remains open']):
   out.append('\n'.join(lines[max(0,i-2):min(len(lines),i+12)]))
 return ident,d['authors'],d['title'],out
with ThreadPoolExecutor(max_workers=4) as ex:
 for result in ex.map(one,selected):
  if result:
   ident,authors,title,out=result
   (L/'sources'/(ident+'-questions.txt')).write_text('\n\n'.join(out))
   print('BODY',ident,authors,title,'\n','\n'.join(out)[-11000:])
