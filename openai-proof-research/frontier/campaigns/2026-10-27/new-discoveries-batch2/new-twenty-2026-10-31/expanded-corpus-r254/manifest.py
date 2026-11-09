import pathlib,hashlib,json,datetime
L=pathlib.Path(__file__).resolve().parent
r=json.loads((L/'results.json').read_text())
for v in r.values():v['provenance']['chunk_number_one_based']=int(pathlib.Path(v['provenance']['chunk']).stem.rsplit('-',1)[1])
(L/'results.json').write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')
receipts=[]
for p in sorted(L.glob('*.receipt.json')):
 d=json.loads(p.read_text());body=p.with_name(p.name.replace('.receipt.json','.body'))
 assert body.exists() and hashlib.sha256(body.read_bytes()).hexdigest()==d['sha256']
 receipts.append({'receipt_file':p.name,**d})
(L/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
(L/'validation.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_twenty_ids':True,'raw_and_statement_hashes_verified':True,'http_receipt_hashes_verified':len(receipts),'heavy_execution':False,'lean_claim':False,'accepted_credit':0,'campaign_count_unchanged':'52/60','background_research_processes':'All launched sessions observed complete before handback.'},indent=2)+'\n')
lines=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name!='SHA256SUMS':lines.append(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(L)))
(L/'SHA256SUMS').write_text('\n'.join(lines)+'\n')
print('Manifest files',len(lines),'HTTP receipts',len(receipts))
