from pathlib import Path
import json,gzip,re,urllib.request,hashlib,datetime
p=Path(__file__).parent;b=p.parent/'root-edge-irregulator-final-freeze-r1';pat=re.compile(r'Entropy.*Concav|Concav.*Entropy|BallNayar|Ball.Nayar|Gaussian.*Smooth|Smooth.*Gaussian|Lamkin|2609.11418|2608.00813',re.I)
out={}
for key,repo,base in [('omega','the-omega-institute/trureturing','1b999d9fda71df7537b62327147496d64a6f66ef'),('openai','openai/math','7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a')]:
 head=json.loads((p/'sources'/f'{key}-head.json').read_text())['sha']; lines=gzip.open(b/f'{key}-tree.txt.gz','rt').read().splitlines();hits=[x for x in lines if pat.search(x)]
 rec={'base':base,'head':head,'base_paths':len(lines),'lexical_hits':hits,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if head!=base:
  url=f'https://api.github.com/repos/{repo}/compare/{base}...{head}'
  try:
   with urllib.request.urlopen(url,timeout=25) as f:raw=f.read(12000000)
   (p/'sources'/f'{key}-delta.json').write_bytes(raw);d=json.loads(raw);rec.update(total_commits=d.get('total_commits'),files_returned=len(d.get('files',[])),matching_delta=[x for x in d.get('files',[]) if pat.search(x['filename']+' '+x.get('patch',''))])
  except Exception as e:rec['delta_error']=str(e)
 out[key]=rec
(p/'registry-audit.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:16000])
