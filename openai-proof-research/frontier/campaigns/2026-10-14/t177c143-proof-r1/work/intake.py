from pathlib import Path
import hashlib,json,shutil,datetime,urllib.request,concurrent.futures
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/t177c143-proof-r1'
A=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r143'
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def dump(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
anchors={'FINAL.json':'9288d77635bae71c1f046d6372286db9785a9370bbc16cface9f9d8e532b1502','MANIFEST.json':'91c271ce12b36624b6123bc9f652c42f0a58ff55dfb9190c94f5330cca2704a6','REPORT.md':'d553e9507b900c6251c33faf75c24bcb670518b8402547fe32a073feabc2ac2b','packet/public/verify.py':'7c0ed9a9bf221dfdff1468f93e6300f6ed875b7feeeb885876f54744003a88d8','packet/public/frozen-scope.md':'cc916afef1373c1b3c0abdee271a4c2769f887f664e8c9b2b16b1b381c0de221','packet/public/author-proof.md':'10e6dda7b9824e629922e3cf6f42de1b2bc194803ace97eb774c7dd85858792a'}
for p,h in anchors.items():assert sha((A/p).read_bytes())==h
tree_bytes=(P/'sources/preprints-tree.json').read_bytes()
assert sha(tree_bytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tree_bytes);assert len(tree['tree'])==13223 and tree['truncated'] is False
index={x['path']:x for x in tree['tree']}
# Explicit incoming-author copy, never a broad search of reviews or other rounds.
dest=R/'packet/private/incoming-author'
assert not dest.exists()
shutil.copytree(A,dest,symlinks=True)
rows=[]
for p in sorted(A.rglob('*')):
 assert not p.is_symlink()
 if p.is_file():
  b=p.read_bytes();assert b==(dest/p.relative_to(A)).read_bytes()
  rows.append({'path':str(p.relative_to(A)),'bytes':len(b),'sha256':sha(b)})
dump(R/'packet/private/incoming-observation.json',{'observed':now(),'external_anchors':anchors,'files':rows,'meaning':'Current incoming bytes; no first-read chronology certificate. Copy not independent semantic evidence.'})
srcs=json.loads((A/'packet/private/upstream-acquisition.json').read_text())
def fetch(x):
 path=x['path'];meta=index[path];old=(A/'packet/private/upstream'/path).read_bytes()
 assert len(old)==meta['size']==x['size']
 blob=hashlib.sha1(b'blob '+str(len(old)).encode()+b'\0'+old).hexdigest()
 assert blob==meta['sha']==x['git_blob'] and sha(old)==x['sha256']
 out={'path':path,'tree_size':meta['size'],'git_blob':blob,'sha256':sha(old),'url':x['url'],'observed':now()}
 try:
  b=urllib.request.urlopen(x['url'],timeout=25).read()
  assert b==old
  p=R/'packet/private/reacquired-upstream'/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
  out['independent_raw_download']='matches complete tree and incoming bytes'
 except Exception as e:out['download_failure']=repr(e)
 return out
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:raw=list(pool.map(fetch,srcs))
dump(R/'packet/private/source-authentication.json',{'tree_sha256':sha(tree_bytes),'tree_entries':len(index),'truncated':tree['truncated'],'files':raw})
# Primary PDFs are authenticated preserved versions, not claimed new downloads.
primary=[]
for x in json.loads((A/'packet/private/primary/acquisition.json').read_text()):
 if 'failure' in x:primary.append(x);continue
 b=(A/'packet/private/primary'/(x['name']+'.pdf')).read_bytes()
 assert len(b)==x['size'] and sha(b)==x['sha256']
 primary.append({**x,'review_observation':now(),'review_capture':'Authenticated incoming PDF; author download time is not reviewer acquisition time.'})
dump(R/'packet/private/primary-authentication.json',primary)
print(json.dumps({'copied_files':len(rows),'raw_files':len(raw),'raw_download_failures':[x for x in raw if 'download_failure' in x]},indent=2))
