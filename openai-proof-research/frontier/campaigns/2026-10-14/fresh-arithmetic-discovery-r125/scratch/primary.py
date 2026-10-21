from pathlib import Path
import urllib.request,json,hashlib,subprocess,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r125')
items=[('lenstra1991','https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf'),('friedl-ronyai1985','https://www.cs.uoregon.edu/Reports/TR-1985-003.pdf'),('ikrs2008','https://arxiv.org/pdf/0811.3165')]
def get(item):
 name,url=item
 try:
  with urllib.request.urlopen(url,timeout=45) as f:b=f.read()
  assert b.startswith(b'%PDF'), 'not a PDF'
  p=R/'private/primary'/f'{name}.pdf';p.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=40)
  return {'name':name,'url':url,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'text_sha256':hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest()}
 except Exception as e:return {'name':name,'url':url,'failure':repr(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:out=list(ex.map(get,items))
(R/'private/primary/identities.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
# Explicit selected companion, no directory crawl.
tree=json.loads(Path('sources/preprints-tree.json').read_bytes())['tree'];pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
rec=json.loads((R/'private/source-identities.json').read_text())
prefix='preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/sections/'
for name in ['01-introduction.tex','07-splitting.tex']:
 x=next(x for x in tree if x['path']==prefix+name);url=f'https://raw.githubusercontent.com/openai/math/{pin}/{x["path"]}'
 with urllib.request.urlopen(url,timeout=45) as f:b=f.read()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==x['sha'] and len(b)==x['size']
 out=R/'private/source'/('companion-'+name);out.write_bytes(b)
 rec.append(dict(canonical=x['path'],url=url,size=len(b),git_blob=blob,sha256=hashlib.sha256(b).hexdigest(),copy=str(out.relative_to(R))))
(R/'private/source-identities.json').write_text(json.dumps(rec,indent=2)+'\n');print('Total authenticated pinned blobs',len(rec))
