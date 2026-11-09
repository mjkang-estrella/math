import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];E=json.loads((D/'extracted.json').read_text());report=[]
for f in sorted({v['provenance']['chunk'] for v in E.values()}):
 P=pathlib.Path(f);targets={v['provenance']['line_1based']:(k,v) for k,v in E.items() if v['provenance']['chunk']==f};h=hashlib.sha256();rows=[]
 with P.open('rb') as inp:
  for lineno,b in enumerate(inp,1):
   h.update(b)
   if lineno in targets:
    k,v=targets[lineno];expected=v['provenance'];ok=b==(D/'raw'/f'{k}.jsonl').read_bytes() and hashlib.sha256(b).hexdigest()==expected['raw_sha256'];assert ok;rows.append(k)
 digest=h.hexdigest();assert all(digest==v['provenance']['chunk_sha256'] for k,v in targets.values());assert len(rows)==len(targets)
 report.append({'chunk':f,'sha256':digest,'raw_ids_verified':rows})
(D/'outputs/resume-provenance-verified.json').write_text(json.dumps(report,indent=2)+'\n');print('Verified original chunk hashes and exact newline-preserving source lines for',len(E),'records')
