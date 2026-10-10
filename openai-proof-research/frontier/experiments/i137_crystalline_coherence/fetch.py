from pathlib import Path
import urllib.request,json,hashlib,subprocess,runpy,sys
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i137_crystalline_coherence';(S/'external').mkdir(exist_ok=True)
ext=runpy.run_path(str(R/'frontier/experiments/i131_soft_summary_stability/extract_html.py'))['extract']
items=[('fjm-2002','https://www.aem.umn.edu/~james/research/Publications_Files/PDF/73.pdf','pdf'),('fks-v2','https://arxiv.org/pdf/2006.01558v2','pdf'),('fkz-v5','https://arxiv.org/pdf/2107.10808v5','pdf'),('fks-current','https://arxiv.org/abs/2006.01558','html'),('fkz-current','https://arxiv.org/abs/2107.10808','html'),('leble-current','https://arxiv.org/abs/2511.03353','html')]
rows=[]
for name,url,kind in items:
 d={'name':name,'url':url,'kind':kind}
 try:
  with urllib.request.urlopen(url,timeout=45) as f:b=f.read();d.update(status=f.status,final_url=f.url)
  p=S/'external'/f'{name}.{kind}';p.write_bytes(b);t=p.with_suffix('.txt')
  if kind=='pdf':
   z=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True);d.update(extraction_command=['pdftotext','-layout',str(p.relative_to(R)),str(t.relative_to(R))],extraction_code=z.returncode,extraction_stderr=z.stderr.decode())
  else:t.write_text(ext(b.decode()))
  d.update(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),text=str(t.relative_to(R)),text_sha256=hashlib.sha256(t.read_bytes()).hexdigest(),lines=len(t.read_text().splitlines()))
 except Exception as e:d.update(error=repr(e))
 rows.append(d);print(name,d.get('status'),d.get('lines'),d.get('error'),flush=True)
(S/'external-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
