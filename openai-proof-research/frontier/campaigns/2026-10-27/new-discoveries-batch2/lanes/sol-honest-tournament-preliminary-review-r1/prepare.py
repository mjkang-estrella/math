import pathlib,json,hashlib,subprocess
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((L/'bindings.json').read_text())
for r in rows:
 if 'original' not in r:continue
 p=pathlib.Path(r['original']);q=pathlib.Path(r['copy']);assert sha(p)==r['sha256']==sha(q)
 if q.parent.name=='primary' and q.name not in ['1803.00823v1.pdf','1803.00823v1.txt']:
  q.unlink();r['immutable_reference']=r.pop('copy');r['reuse_policy']='not copied in final packet; original remains hash-bound; not read for this review'
(L/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
for r in map(json.loads,(L/'access.jsonl').read_text().splitlines()):
 if 'path' in r:assert sha(pathlib.Path(r['path']))==r['sha256']
p=L/'current/chalmers.pdf'
assert p.read_bytes().startswith(b'%PDF')
print('Chalmers PDF same bytes as v1:',sha(p)==sha(L/'frozen/primary/1803.00823v1.pdf'))
subprocess.run(['pdftotext','-layout',str(p),str(L/'current/chalmers.txt')],check=True)
(L/'current/chalmers-text-binding.json').write_text(json.dumps({'pdf_sha256':sha(p),'text_sha256':sha(L/'current/chalmers.txt'),'same_pdf_as_arxiv_v1':sha(p)==sha(L/'frozen/primary/1803.00823v1.pdf')},indent=2)+'\n')
