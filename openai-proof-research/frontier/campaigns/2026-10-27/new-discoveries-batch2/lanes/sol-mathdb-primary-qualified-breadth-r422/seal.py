import pathlib,json,hashlib
O=pathlib.Path(__file__).parent
body={393113,393127,393149,393159,393190,393203,393224,393658,393659,393667,393668,393669,393677,393678}
p=O/'dispositions.json';ds=json.loads(p.read_text())
for d in ds:d['evidence_levels']['primary_problem_body_read']=d['mathdb_id'] in body
p.write_text(json.dumps(ds,ensure_ascii=False,indent=2)+'\n')
p=O/'assignment-check.json';v=json.loads(p.read_text());v['primary_sections_read']=len(body);p.write_text(json.dumps(v,indent=2)+'\n')
p=O/'SUMMARY.md';s=p.read_text().replace('Sixteen source-section inspections','Fourteen source-section inspections');p.write_text(s)
p=O/'provenance.json';v=json.loads(p.read_text());v['external_proof_body_read']['retention']='retained-successor.json';p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
p=O/'failures.json';v=json.loads(p.read_text());r=json.loads((O/'retained-successor.json').read_text())
if 'error' in r:v.append(r)
p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in {'manifest.json','final-receipt.json'}:files.append({'path':str(p.relative_to(O)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size})
(O/'manifest.json').write_text(json.dumps({'excluded_exact_relative_paths':['manifest.json','final-receipt.json'],'files':files},indent=2)+'\n')
print('sealed',len(files),'payload files; successor',r)
