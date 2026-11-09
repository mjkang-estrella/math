import json,hashlib,urllib.request,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]; repo=ROOT.parents[3]
TREE=json.loads((repo/'sources/preprints-tree.json').read_text()); assert len(TREE['tree'])==13223 and TREE['truncated'] is False
ENT={a['path']:a for a in TREE['tree']}; PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
regpath=ROOT/'packet/public/source-register.json'
reg=json.loads(regpath.read_text()) if regpath.exists() else []
def fetch(prefix,suffix,alias):
 match=[p for p in ENT if p.startswith('preprints/'+prefix) and p.endswith(suffix)]; assert len(match)==1,match
 p=match[0]; url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{p}'; b=urllib.request.urlopen(url,timeout=45).read(); a=ENT[p]
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==a['sha']; assert len(b)==a['size']
 out=ROOT/'packet/private/sources'/alias; out.write_bytes(b)
 reg.append({'alias':alias,'path':p,'url':url,'blob':a['sha'],'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'local':str(out.relative_to(ROOT/'packet'))})
 regpath.write_text(json.dumps(reg,indent=2)+'\n'); print(alias,len(b),flush=True)
if __name__=='__main__':
 import sys
 fetch(*sys.argv[1:])
