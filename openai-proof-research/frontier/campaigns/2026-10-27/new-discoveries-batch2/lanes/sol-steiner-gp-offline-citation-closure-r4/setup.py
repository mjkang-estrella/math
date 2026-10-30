import pathlib,json,hashlib,shutil,datetime
HERE=pathlib.Path(__file__).resolve().parent
LANES=HERE.parent
def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(name,x): (HERE/name).write_text(json.dumps(x,indent=2)+'\n')
def main():
 records=[];freezes=[]
 for label in ['root-steiner-gp-gap-hold-r3','root-r165-preliminary-freeze-r1']:
  p=LANES/label/'review-freeze.json';data=json.loads(p.read_text());freezes.append({'path':str(p),'sha256':sha(p),'count':len(data['files'])})
  for r in data['files']:
   src=pathlib.Path(r['path']);assert src.stat().st_size==r['bytes'] and sha(src)==r['sha256'],str(src)
   rel=src.relative_to(LANES);dst=HERE/'inputs'/rel;dst.parent.mkdir(parents=True,exist_ok=True)
   # One independent copy per frozen path; no subsequent duplicate merge diffs.
   shutil.copyfile(src,dst);assert sha(dst)==r['sha256']
   records.append({**r,'copy':str(dst.relative_to(HERE))})
  dst=HERE/'inputs'/label/'review-freeze.json';dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst)
 save('before.json',{'utc':utc(),'freezes':freezes,'files':records})
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md','AGENTS.md']:
  shutil.copyfile(LANES.parent/n,HERE/('context-'+n))
 save('guard-binding.json',{'utc':utc(),'path':str(LANES/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'sha256':sha(LANES/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')})
 print(json.dumps({'freezes':freezes,'copies':len(records),'bytes':sum(r['bytes'] for r in records)}))
if __name__=='__main__':main()
