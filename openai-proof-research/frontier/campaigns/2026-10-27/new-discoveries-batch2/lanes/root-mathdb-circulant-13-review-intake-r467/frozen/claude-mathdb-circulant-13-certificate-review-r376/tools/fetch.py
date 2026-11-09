# Fetch one public URL into its own new directory; record URL/UTC/status/sha; detect 403/429/challenge before any content use. No retries.
import subprocess,sys,hashlib,json,datetime,re
from pathlib import Path
name,url,outroot=sys.argv[1],sys.argv[2],Path(sys.argv[3])
d=outroot/name; d.mkdir(parents=True,exist_ok=False)
utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
r=subprocess.run(['curl','-sS','-L','--max-time','60','--max-filesize','20000000','-A','Mozilla/5.0 (research; mj.kang lane r376)','-D',str(d/'headers'),'-o',str(d/'body'),'-w','%{http_code}\t%{content_type}\t%{url_effective}',url],capture_output=True,text=True)
code,ctype,eff=(r.stdout.split('\t')+['','',''])[:3]
b=(d/'body').read_bytes() if (d/'body').exists() else b''
low=b[:200000].lower()
chal=any(k in low for k in [b'captcha',b'cf-chl',b'challenge-platform',b'are you a robot',b'access denied',b'just a moment'])
st='ok' if code=='200' and not chal else ('HOLD-'+code if code in('403','429') else ('challenge-suspected' if chal else 'error-'+code))
rec={'name':name,'url':url,'effective_url':eff,'utc':utc,'http_status':code,'content_type':ctype,'curl_exit':r.returncode,'stderr':r.stderr.strip(),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'challenge_suspected':chal,'status':st}
(d/'record.json').write_text(json.dumps(rec,indent=1)+'\n'); print(json.dumps(rec))
