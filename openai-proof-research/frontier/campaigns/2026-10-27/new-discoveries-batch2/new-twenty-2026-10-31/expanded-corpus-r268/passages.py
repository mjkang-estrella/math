from pathlib import Path
import subprocess,resource,json,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;r=json.loads((p/'receipts-pdf-urls.json').read_text());out=[]
for d in r:
 f=p/d['path'];t=Path(str(f)+'.txt');q=subprocess.run(['pdftotext','-layout',str(f),str(t)],capture_output=True,timeout=10);d.update(text_path=str(t.relative_to(p)),pdftotext_returncode=q.returncode)
 lines=t.read_text().splitlines();ix=[i for i,l in enumerate(lines) if 'conjectur' in l.lower()];keep=set()
 for i in ix:keep.update(range(max(0,i-2),min(len(lines),i+12)))
 out.append('\nFILE '+t.name+'\n'+'\n'.join(f'{i+1}: {lines[i]}' for i in sorted(keep)))
(p/'receipts-pdf-urls.json').write_text(json.dumps(r,indent=2)+'\n');(p/'version-passages.txt').write_text('\n'.join(out));print('completed',len(r),'CPU',time.process_time())
