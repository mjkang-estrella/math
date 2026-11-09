from pathlib import Path
import urllib.request,json,datetime,hashlib,sys
P=Path(__file__).resolve().parent
M=P/'provenance.json'
def get(n,u):
 r={'file':n,'url':u,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=35) as f: b=f.read(16000000);r['status']=f.status
  (P/'sources'/n).write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));out=b
 except Exception as e:r['error']=str(e);out=None
 m=json.loads(M.read_text()) if M.exists() else {'retrievals':[]};m['retrievals'].append(r);M.write_text(json.dumps(m,indent=2));return out
if __name__=='__main__':get(sys.argv[1],sys.argv[2])
