# Sequential, polite fetcher. Writes into sources/<subdir>/ with receipts. Never retries a 403/429.
import pathlib,json,hashlib,datetime,urllib.request,urllib.error,sys,time
D=pathlib.Path(__file__).resolve().parents[1]
def get(key,url,sub='web'):
 d=D/'sources'/sub; d.mkdir(parents=True,exist_ok=True); p=d/key; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification (non-commercial)'}),timeout=25) as r: data=r.read(); status=r.status; final=r.url; ctype=r.headers.get('Content-Type')
  p.write_bytes(data); rec=dict(url=url,final_url=final,status=status,content_type=ctype,utc=now,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p.relative_to(D)))
 except urllib.error.HTTPError as e: rec=dict(url=url,utc=now,status=e.code,error=str(e))
 except Exception as e: rec=dict(url=url,utc=now,error=repr(e))
 (d/f'{key}.receipt.json').write_text(json.dumps(rec,indent=2)+'\n'); print(key,rec.get('status'),rec.get('bytes'),rec.get('error',''),flush=True); return rec
if __name__=='__main__':
 sub=sys.argv[1]; items=json.loads(sys.argv[2])
 for k,u in items:
  r=get(k,u,sub)
  if r.get('status') in (403,429): print('STOP: access refusal, not retrying',flush=True); break
  time.sleep(1.5)
