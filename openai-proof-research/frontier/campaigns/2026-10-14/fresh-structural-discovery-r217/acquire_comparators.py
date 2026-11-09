from pathlib import Path
import json,urllib.request,hashlib,concurrent.futures,subprocess
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r217');P=R/'private';PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
(P/'primary').mkdir(exist_ok=True)
entries=json.loads((P/'companion-tree-selection.json').read_text());blobs=[x for x in entries if x['type']=='blob']
def fetch(x):
 url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path']
 with urllib.request.urlopen(url,timeout=40) as f:b=f.read()
 sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert sha==x['sha'] and len(b)==x['size']
 p=P/x['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return {'path':x['path'],'url':url,'sha256':hashlib.sha256(b).hexdigest(),'git_blob':sha,'bytes':len(b)}
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:records=list(pool.map(fetch,blobs))
(P/'companion-authentication.json').write_text(json.dumps(records,indent=2)+'\n');print('Companions authenticated:',len(records))
urls={
 'Donaldson2006':'https://arxiv.org/pdf/math/0607083v1',
 'FineLotaySinger':'https://arxiv.org/pdf/1603.08170',
 'FineYao2017':'https://arxiv.org/pdf/1704.07620v2',
 'LiLiu2001':'https://arxiv.org/pdf/math/0107211v2',
 'Taubes1999':'https://arxiv.org/pdf/math/9907199v1',
 'GrossWilson2000':'https://arxiv.org/pdf/math/0008018v3',
 'LiZhang2009':'https://arxiv.org/pdf/0708.2520',
 'McLean1998':'https://intlpress.com/site/pub/files/_fulltext/journals/cag/1998/0006/0004/CAG-1998-0006-0004-a004.pdf'
}
def primary(item):
 name,url=item
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'r217-research'}),timeout=40) as f:b=f.read();resolved=f.url
  assert b.startswith(b'%PDF'), 'not a PDF'
  p=P/'primary'/(name+'.pdf');p.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,capture_output=True)
  t=p.with_suffix('.txt').read_bytes()
  return {'name':name,'url':url,'resolved':resolved,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'text_bytes':len(t),'pages':t.count(b'\f'),'status':'downloaded; not yet semantically read'}
 except Exception as e:return {'name':name,'url':url,'error':str(e),'coverage':'none'}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:results=list(pool.map(primary,urls.items()))
(P/'primary-access.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
