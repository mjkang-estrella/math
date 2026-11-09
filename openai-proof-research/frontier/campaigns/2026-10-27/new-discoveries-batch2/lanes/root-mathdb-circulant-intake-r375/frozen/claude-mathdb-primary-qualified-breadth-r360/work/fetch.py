# Lawful primary HTTP fetch. One new directory per retrieved item; stop on 403/429/challenge, no retry.
import sys,subprocess,hashlib,json,datetime
from pathlib import Path
L=Path(__file__).resolve().parents[1]; log=L/'source-provenance.json'
rows=json.loads(log.read_text()) if log.exists() else []
name,url=sys.argv[1],sys.argv[2]
d=L/'sources'/name; assert not d.exists(),d; d.mkdir(parents=True)
out=d/'body'; utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
r=subprocess.run(['curl','-sS','-L','--max-time','60','--max-filesize','30000000','-A','research-fetch/1.0 (mailto withheld)','-o',str(out),'-w','%{http_code}\t%{content_type}\t%{url_effective}',url],capture_output=True,text=True)
code,ctype,eff=(r.stdout.split('\t',2)+['','',''])[:3]
row={'name':name,'url':url,'effective_url':eff,'utc':utc,'http_status':code,'content_type':ctype,'curl_exit':r.returncode,'stderr':r.stderr[-300:]}
if out.exists():
    b=out.read_bytes(); row.update(size=len(b),sha256=hashlib.sha256(b).hexdigest())
    low=b[:4000].lower()
    row['challenge_suspected']=any(s in low for s in [b'captcha',b'challenge',b'are you a robot',b'access denied'])
row['status']='ok' if code=='200' and not row.get('challenge_suspected') else 'FAILED_STOP_NO_RETRY'
rows.append(row); log.write_text(json.dumps(rows,indent=1)+'\n'); print(json.dumps(row))
