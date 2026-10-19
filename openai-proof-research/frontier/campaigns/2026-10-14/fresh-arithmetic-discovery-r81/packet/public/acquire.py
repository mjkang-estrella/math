"""Fetch explicitly selected canonical blobs; writes only into this packet."""
import json,hashlib,urllib.request, pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[2]
REPO=ROOT.parents[3]
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def main():
 tree=json.loads((REPO/'sources/preprints-tree.json').read_text())
 assert len(tree['tree'])==13223 and tree['truncated'] is False
 entries={e['path']:e for e in tree['tree'] if e['type']=='blob'}
 receipt=ROOT/'packet/private/source-provenance.json'
 old=json.loads(receipt.read_text()) if receipt.exists() else []
 for raw in sys.stdin:
  p=raw.strip()
  if not p: continue
  e=entries[p]; url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{p}'
  data=urllib.request.urlopen(url,timeout=60).read()
  blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
  assert blob==e['sha']
  loc='packet/private/upstream/'+p
  out=ROOT/loc;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(data)
  r={'path':p,'raw_url':url,'git_blob':blob,'sha256':hashlib.sha256(data).hexdigest(),'size':len(data),'local':loc}
  old=[a for a in old if a['path']!=p]+[r]
  print(p,len(data))
 receipt.write_text(json.dumps(old,indent=2)+'\n')
if __name__=='__main__':main()
