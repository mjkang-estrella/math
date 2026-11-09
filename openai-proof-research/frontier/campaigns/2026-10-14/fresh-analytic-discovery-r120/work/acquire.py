from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
ROOT=Path(__file__).resolve().parents[1]
NAV=json.loads((ROOT/'work/navigation2.json').read_text())
want={'078':['01-introduction.tex','12-multiplier.tex'],'083':['01-introduction.tex','02-reductions.tex','11-assembly.tex'],'090':['06-gaussian-energy-transfer.tex','07-shifted-mixtures.tex','08-renormalized-jellium.tex'],'219':['01-introduction.tex','02-tree.tex','04-marked-entropy.tex'],'341':['01-introduction.tex','05-families.tex','11-endpoint.tex'],'366':['introduction.tex','reductions.tex','completion.tex']}
entries=[e for e in NAV if Path(e['path']).name in want[e['family']] and not (e['family']=='219' and 'Fixed-energy-' not in e['path'])]
def get(e):
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path'];b=urllib.request.urlopen(url,timeout=50).read();h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert h==e['sha'];dest='private/upstream/'+e['family']+'/'+Path(e['path']).name;p=ROOT/'packet'/dest;p.parent.mkdir(exist_ok=True,parents=True);p.write_bytes(b)
 return {'family':e['family'],'path':e['path'],'url':url,'git_blob':h,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'local':dest,'reading':'acquired; semantic extent pending'}
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex: results=list(ex.map(get,entries))
(ROOT/'packet/public/source-register.json').write_text(json.dumps(results,indent=2)+'\n')
print('acquired',len(results),'bytes',sum(e['bytes'] for e in results))
