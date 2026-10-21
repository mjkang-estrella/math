from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
ROOT=Path(__file__).resolve().parents[1]; P=ROOT.parents[3]
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads((P/'sources/preprints-tree.json').read_text())['tree']
selected=[x for x in tree if x['type']=='blob' and x['path'].endswith(('.tex','.bib')) and any(f in x['path'] for f in ['A-power-saving-for-intersective-polynomial','A-Power-Saving-for-Polynomial-Differences','A-power-saving-for-square-difference'])]
def fetch(x):
 url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path']
 out=ROOT/'private/sources'/x['path'];out.parent.mkdir(parents=True,exist_ok=True)
 try:
  with urllib.request.urlopen(url,timeout=40) as r:b=r.read(); final=r.url
  sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert len(b)==x['size'] and sha==x['sha']
  out.write_bytes(b)
  return dict(path=x['path'],url=url,final_url=final,bytes=len(b),git_blob=sha,sha256=hashlib.sha256(b).hexdigest(),status='authenticated')
 except Exception as e:return dict(path=x['path'],url=url,status='failed',error=repr(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: result=list(ex.map(fetch,selected))
(ROOT/'private/source-polynomial-metadata.json').write_text(json.dumps(result,indent=2))
print('acquired',len(result),'failed',[x for x in result if x['status']!='authenticated'])
