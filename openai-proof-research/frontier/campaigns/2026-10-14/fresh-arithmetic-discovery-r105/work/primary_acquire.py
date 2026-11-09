from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r105'; D=R/'packet/private'; rec=[]
for v in ['0912.0574v1','1010.3528v2','1710.01469v1','1901.06704v3']:
 url='https://arxiv.org/pdf/'+v
 try:
  b=urllib.request.urlopen(url,timeout=45).read();assert b.startswith(b'%PDF')
  p=D/'primary'/f'{v}.pdf';p.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  rec.append(dict(url=url,version=v,size=len(b),sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 except Exception as e:rec.append(dict(url=url,error=str(e)))
(D/'primary/receipts.json').write_text(json.dumps(rec,indent=2)+'\n')
T=json.loads((P/'sources/preprints-tree.json').read_text())['tree'];a=json.loads((D/'sources/acquisition.json').read_text())
for e in T:
 p=e['path']
 if 'A-counterexample-to-Tachikawas-second' not in p or not any(p.endswith('/'+f) for f in ['introduction.tex','consequences.tex']):continue
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+p
 b=urllib.request.urlopen(url,timeout=45).read(); g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert g==e['sha'] and len(b)==e['size']
 dest=D/'sources'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 a.append(dict(path=p,url=url,size=len(b),git_blob_sha1=g,sha256=hashlib.sha256(b).hexdigest(),acquired_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),read=False))
(D/'sources/acquisition.json').write_text(json.dumps(a,indent=2)+'\n')
print(rec)
