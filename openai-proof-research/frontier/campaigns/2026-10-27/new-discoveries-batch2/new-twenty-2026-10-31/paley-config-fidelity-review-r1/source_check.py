import pathlib,json,hashlib,tarfile,gzip,re
D=pathlib.Path(__file__).resolve().parent;A=D.parent/'expanded-corpus-r49';rec={}
for id in ['355956','355701']:
 r=json.loads((A/'results.json').read_text())[id];p=r['provenance'];data=pathlib.Path(p['chunk']).read_bytes();line=data.splitlines(keepends=True)[p['line_1based']-1];assert hashlib.sha256(data).hexdigest()==p['chunk_sha256'];assert hashlib.sha256(line).hexdigest()==p['raw_sha256'];assert line==(A/r['raw_file']).read_bytes();row=json.loads(line);assert row['statement']==r['literal_statement'];assert hashlib.sha256(row['statement'].encode()).hexdigest()==p['statement_sha256'];rec[id]={'raw':p,'statement_exact':True}
for name,body in [('2101.09652','main.tex'),('2209.00864','main.tex'),('2208.06912','template.tex')]:
 p=A/f'sources/{name}.tar'
 try:
  with tarfile.open(p) as t:
   matches=[m for m in t.getmembers() if m.name==body or m.name.endswith('/'+body)];assert len(matches)==1; data=t.extractfile(matches[0]).read()
 except tarfile.ReadError:data=gzip.decompress(p.read_bytes())
 assert data==(A/f'sources/x-{name}/{body}').read_bytes()
 rec[name]={'body_correspondence':True,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
receipts=[json.loads(l) for l in (A/'receipts.jsonl').read_text().splitlines()]
rec['primary_http_receipts']=[r for r in receipts if any(s in str(r) for s in ['2101.09652','2209.00864','2208.06912','ALCO_2023','ejgta-1710'])]
(D/'literal-source-check.json').write_text(json.dumps(rec,indent=2))
