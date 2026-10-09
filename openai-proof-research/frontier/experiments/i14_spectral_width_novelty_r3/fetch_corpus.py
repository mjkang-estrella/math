import pathlib,json,hashlib,concurrent.futures,urllib.request,time
root=pathlib.Path('.'); out=root/'frontier/sources/i14_spectral_width_novelty_r3'; pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb';tree=json.load(open('sources/preprints-tree.json'))['tree']; selected=[e for e in tree if e['type']=='blob' and e['path'].endswith(('.tex','.bib','.md','.txt'))]; manifest=[]
# Search all textual manuscripts, not merely title-selected companions.
def run(e):
 p=e['path'];q=out/'corpus'/p;q.parent.mkdir(parents=True,exist_ok=True);url='https://raw.githubusercontent.com/openai/math/'+pin+'/'+urllib.parse.quote(p)
 try:
  if q.exists(): b=q.read_bytes()
  else:
   for attempt in range(3):
    try:
     b=urllib.request.urlopen(url,timeout=40).read();break
    except Exception:
     if attempt==2: raise
     time.sleep(1)
  blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==e['sha'],(p,blob,e['sha']);q.write_bytes(b)
  return {'path':p,'url':url,'git_blob':blob,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'status':'verified'}
 except Exception as ex:return {'path':p,'url':url,'status':'error','error':str(ex)}
with concurrent.futures.ThreadPoolExecutor(max_workers=32) as pool:
 for i,item in enumerate(pool.map(run,selected)):
  manifest.append(item)
  if (i+1)%500==0: print(i+1,'/',len(selected),flush=True)
(out/'corpus-manifest.json').write_text(json.dumps({'pin':pin,'files':manifest},indent=2)+'\n');print('DONE',len(manifest),'errors',sum(x['status']!='verified' for x in manifest),flush=True)
