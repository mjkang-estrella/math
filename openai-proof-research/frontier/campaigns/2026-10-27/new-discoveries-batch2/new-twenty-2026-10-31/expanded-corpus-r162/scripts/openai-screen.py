import pathlib,json,urllib.request,datetime,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1]
def fetch(label,url):
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 try:
  with urllib.request.urlopen(url,timeout=20) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest())
  (D/f'sources/{label}.json').write_bytes(b);o=json.loads(b)
 except Exception as e:r['error']=str(e);o={}
 (D/f'sources/{label}.receipt.json').write_text(json.dumps(r,indent=2));return o
head=json.loads((D/'sources/registry-math.json').read_text())['sha']
root=fetch('openai-root','https://api.github.com/repos/openai/math/git/trees/'+head)
ent=next((x for x in root.get('tree',[]) if x['path']=='preprints'),None)
out={'head':head,'preprints_present':bool(ent)}
if ent:
 o=fetch('openai-preprints','https://api.github.com/repos/openai/math/git/trees/'+ent['sha']+'?recursive=1')
 ps=[x['path'] for x in o.get('tree',[])]
 out.update(truncated=o.get('truncated'),paths=len(ps),hits=[p for p in ps if re.search('nanostar|totient|Ghanbari|cordial|Mousley|interweaving|matching.sequenc|correlation.immun',p,re.I)])
(D/'outputs/openai-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
