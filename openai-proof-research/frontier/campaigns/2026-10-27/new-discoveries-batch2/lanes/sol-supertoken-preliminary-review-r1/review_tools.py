import pathlib,json,hashlib,datetime,shutil,sys
B=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
R=B/'lanes/sol-supertoken-preliminary-review-r1'
F=B/'lanes/root-supertoken-review-freeze-r1/review-freeze.json'
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''): h.update(b)
 return h.hexdigest()
if __name__=='__main__':
 data=json.loads(F.read_text()); src=pathlib.Path(data['candidate']); results=[]
 for e in data['files']:
  p=src/e['path']; results.append({'path':e['path'],'ok':p.stat().st_size==e['bytes'] and digest(p)==e['sha256']})
 mode=sys.argv[1]
 receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'freeze_sha256':digest(F),'entries':len(results),'all_ok':all(e['ok'] for e in results),'results':results}
 (R/('freeze-'+mode+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
 assert receipt['all_ok']
 if mode=='before':
  for name in ['PROOF.md','discovery.md','provenance.json','fetch-receipts.jsonl','sources/metric-primary.txt','sources/metric-primary.pdf','sources/metric-primary.html','sources/metric-arxiv.html','sources/metric-successor.html','sources/bailey-cameron.txt','sources/bailey-cameron.pdf']:
   target=R/'copy'/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src/name,target)
 print(json.dumps({k:v for k,v in receipt.items() if k!='results'}))
