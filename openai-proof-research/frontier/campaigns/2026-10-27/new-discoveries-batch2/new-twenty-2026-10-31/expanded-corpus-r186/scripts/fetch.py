import pathlib,urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys,time
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186')
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,*a,**k): return None
op=urllib.request.build_opener(NoRedirect)
def fetch(url,label):
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'); base=L/'sources'/f'{stamp}-{label}'; receipt={'url':url,'utc':stamp}
 try:
  with op.open(urllib.request.Request(url,headers={'User-Agent':'MathematicsResearch/1.0'}),timeout=22) as r: data=r.read();receipt.update(status=r.status,headers=dict(r.headers))
 except urllib.error.HTTPError as e: data=e.read();receipt.update(status=e.code,headers=dict(e.headers))
 except Exception as e: data=b'';receipt.update(error=repr(e))
 receipt['sha256']=hashlib.sha256(data).hexdigest();receipt['body']=str(base)+'.body';base.with_suffix('.body').write_bytes(data);base.with_suffix('.json').write_text(json.dumps(receipt,indent=2));print(label,receipt.get('status',receipt.get('error')),len(data),flush=True); return data,receipt
if __name__=='__main__':
 if sys.argv[1]=='abs':
  rows=json.loads((L/'reservation.json').read_text())['rows']
  for r in rows: fetch(r['source_url'],str(r['mathdb_id'])+'-abs')
 else: fetch(sys.argv[1],sys.argv[2])
