from pathlib import Path
import urllib.request,concurrent.futures,hashlib,json,subprocess,re
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r220');P=R/'private/primary';P.mkdir(exist_ok=True)
items=[
('McKay2016','https://arxiv.org/pdf/1309.1326v5'),
('Berger1980','https://www.numdam.org/item/10.5802/aif.802.pdf'),
('RovenskiiToponogov1996','https://arxiv.org/pdf/dg-ga/9609007v1'),
('Yang1991','https://msp.org/pjm/1991/151-2/pjm-v151-n2-p14-p.pdf'),
('Szabo1988','https://archive.mpim-bonn.mpg.de/3787/1/preprint_1988_32.pdf'),
('Weinstein1974','https://projecteuclid.org/journals/journal-of-differential-geometry/volume-9/issue-4/On-the-volume-of-manifolds-all-of-whose-geodesics-are/10.4310/jdg/1214432547.pdf'),
('OttosenBokstedt2007','https://msp.org/agt/2007/7-4/agt-v7-n4-p18-s.pdf'),
('Kazdan1978','https://link.springer.com/content/pdf/10.1007/978-3-642-61876-5_14.pdf'),
('Wilking2001','https://link.springer.com/content/pdf/10.1007/s002220100123.pdf'),
('Szabo1990','https://projecteuclid.org/journals/journal-of-differential-geometry/volume-31/issue-1/The-Lichnerowicz-conjecture-on-harmonic-manifolds/10.4310/jdg/1214444087.pdf')]
def fetch(item):
 name,url=item;r=dict(name=name,url=url)
 try:
  with urllib.request.urlopen(url,timeout=35) as f:b=f.read();r['resolved_url']=f.url
  r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());r['pdf']=b.startswith(b'%PDF')
  if not r['pdf']:r['access']='non-PDF response';return r
  p=P/(name+'.pdf');p.write_bytes(b);txt=P/(name+'.txt');c=subprocess.run(['pdftotext','-layout',str(p),str(txt)],capture_output=True,timeout=25);r['pdftotext_returncode']=c.returncode
  if c.returncode==0:
   t=txt.read_bytes();r.update(text_bytes=len(t),lines=len(t.splitlines(keepends=True)),formfeeds=t.count(b'\f'));r['text_sha256']=hashlib.sha256(t).hexdigest()
  r['access']='downloaded'
 except Exception as e:r['access']=type(e).__name__+': '+str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:rs=list(ex.map(fetch,items))
(P/'access.json').write_text(json.dumps(rs,indent=2)+'\n')
for r in rs:print(json.dumps(r))
