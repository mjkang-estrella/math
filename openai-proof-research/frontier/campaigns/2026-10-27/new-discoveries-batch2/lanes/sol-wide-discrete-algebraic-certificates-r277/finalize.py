from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sources=[]
for p in sorted((L/'sources').glob('*.pdf')):
 t=p.with_suffix('.txt')
 sources.append(dict(id=p.stem,url='https://arxiv.org/pdf/'+p.stem,pdf_sha256=sha(p),text_sha256=sha(t),pdf_bytes=p.stat().st_size,text_bytes=t.stat().st_size))
(L/'source-access-bindings.json').write_text(json.dumps(dict(primary=sources,metadata='chronology.json; sources/all-versions.xml',limits='Current public registry UNKNOWN. No denied routes requested. All arXiv PDF requests succeeded.',frozen_history='bindings.json',administrative='admin snapshot only'),indent=2))
rows=json.loads((L/'bindings.json').read_text())
for row in rows:
 p=Path(row['original']);assert sha(p)==row['sha256'],str(p)
 if 'copy' in row:assert sha(L/row['copy'])==row['sha256']
(L/'MANIFEST.json').write_text(json.dumps({str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']},indent=2))
print('sources',len(sources),'original bindings',len(rows),'manifest finalized')
