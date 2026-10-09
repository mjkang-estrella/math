import concurrent.futures, json, subprocess, urllib.request
from evidence import OUT, ROOT, sha, stamp, write
SOURCES = {
 'ford-v4': 'https://arxiv.org/pdf/2408.03803v4',
 'timofeev-1992': 'https://www.mathnet.ru/links/c5e5f217b843847a9b700696cd9b3630/im971_eng.pdf',
 'granville-shao-v1': 'https://arxiv.org/pdf/1706.05710v1',
 'selberg-delange-v8': 'https://arxiv.org/pdf/2010.12929v8',
 'bharadwaj-rodgers-v4': 'https://arxiv.org/pdf/2402.11884v4',
 'hildebrand-publisher': 'https://londmathsoc.onlinelibrary.wiley.com/doi/pdf/10.1112/plms/s3-59.2.209',
 'elliott-1994': 'https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/0886-01.pdf',
}
def get(item):
 name,url=item; row=dict(name=name,url=url,retrieved_utc=stamp())
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'})
  r=urllib.request.urlopen(req,timeout=45); b=r.read(); row.update(status=r.status,final_url=r.url,bytes=len(b),sha256=sha(b))
  dest=OUT/'literature'/f'{name}.pdf'; dest.parent.mkdir(parents=True,exist_ok=True)
  if not b.startswith(b'%PDF'): raise ValueError('Not a PDF')
  dest.write_bytes(b); row['local']=str(dest.relative_to(ROOT))
  txt=dest.with_suffix('.txt'); subprocess.run(['pdftotext','-layout',str(dest),str(txt)],check=True)
  row['text_sha256']=sha(txt.read_bytes())
 except Exception as exc: row['error']=str(exc)
 return row
if __name__=='__main__':
 with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool: records=list(pool.map(get,SOURCES.items()))
 write('literature-manifest.json',records)
 print(json.dumps(records,indent=2))
