from setup import *
import re,ctypes as C
R=HERE/'inputs/sol-steiner-gp-fixed-gap-closure-r3'
intervals=json.loads((R/'interval-commits.json').read_text())
g=C.CDLL('/usr/lib64/libgit2.so.1.9');g.git_libgit2_init();repo=C.c_void_p()
g.git_repository_open.argtypes=[C.POINTER(C.c_void_p),C.c_char_p]
assert g.git_repository_open(C.byref(repo),str(LANES/'root-edge-irregulator-current-prior-r1/omega.git').encode())==0
g.git_object_lookup.argtypes=[C.POINTER(C.c_void_p),C.c_void_p,C.c_void_p,C.c_int];g.git_object_free.argtypes=[C.c_void_p]
def has(oid):
 obj=C.c_void_p();rc=g.git_object_lookup(C.byref(obj),repo,C.create_string_buffer(bytes.fromhex(oid)), -2)
 if rc==0:g.git_object_free(obj)
 return rc==0
out=[]
for interval in intervals:
 for c in interval['commits']:
  p=R/'retrieved/patches'/(c['sha']+'.patch'); heads=[];blocks=0;idx=[]
  if p.exists():
   with p.open(errors='replace') as f:
    for l in f:
     if re.match(r'^From [0-9a-f]{40} Mon Sep',l):heads.append(l.split()[1])
     if l.startswith('diff --git '):blocks+=1
     if l.startswith('index '):idx.append(l.strip())
  out.append({**c,'commit_available':has(c['sha']),'tree_available':has(c['tree']),'parent_available':{x:has(x) for x in c['parents']},'mail_commits':heads,'patch_blocks':blocks,'index_examples':idx[:3]})
save('cache-inspection.json',{'utc':utc(),'commits':out})
print(json.dumps(out,indent=2))
# Locate the actual retained full 19-record set, rather than guessing authors.
for p in (R/'retrieved').rglob('*.json'):
 if p.stat().st_size>20000000:continue
 try:d=json.loads(p.read_text())
 except (ValueError,UnicodeError):continue
 records=d.get('results',[]) if isinstance(d,dict) else d if isinstance(d,list) else []
 for r in records:
  if not isinstance(r,dict):continue
  if any(x in str(r.get('doi','')) for x in ['2024.04.029','2026.01.008']):
   print('RECORD',p.relative_to(HERE),json.dumps(r));save('record-'+('10' if '2024.04.029' in str(r.get('doi')) else '19')+'.json',r)
