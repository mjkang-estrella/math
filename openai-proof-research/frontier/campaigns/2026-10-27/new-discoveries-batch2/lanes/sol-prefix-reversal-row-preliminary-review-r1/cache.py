import json,ctypes as C,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parent.parent
P=B/'lanes/sol-pendulum-investment-review-r3/research/blueprint.json'
d=json.loads(P.read_text());print('tree metadata',[(k,v) for k,v in d.items() if k!='tree'] if isinstance(d,dict) else type(d))
entries=d.get('tree',[]) if isinstance(d,dict) else d
g=C.CDLL('/usr/lib64/libgit2.so.1.9');g.git_libgit2_init();repo=C.c_void_p()
g.git_repository_open.argtypes=[C.POINTER(C.c_void_p),C.c_char_p]
cache=B/'lanes/root-edge-irregulator-current-prior-r1/omega.git'
assert g.git_repository_open(C.byref(repo),str(cache).encode())==0
g.git_object_lookup.argtypes=[C.POINTER(C.c_void_p),C.c_void_p,C.c_void_p,C.c_int]
g.git_object_free.argtypes=[C.c_void_p]
g.git_blob_rawsize.argtypes=[C.c_void_p];g.git_blob_rawsize.restype=C.c_size_t
g.git_blob_rawcontent.argtypes=[C.c_void_p];g.git_blob_rawcontent.restype=C.c_void_p
out=[]
for e in entries:
 if 'PrefixReversal' not in e.get('path','') or e.get('type')!='blob':continue
 obj=C.c_void_p();rc=g.git_object_lookup(C.byref(obj),repo,C.create_string_buffer(bytes.fromhex(e['sha'])),3)
 r=dict(e,lookup_rc=rc)
 if rc==0:
  size=g.git_blob_rawsize(obj);assert size<2000000
  data=C.string_at(g.git_blob_rawcontent(obj),size);g.git_object_free(obj)
  q=L/'prior-bodies'/e['path'];q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data)
  r.update(copy=str(q.relative_to(L)),sha256=hashlib.sha256(data).hexdigest())
 out.append(r)
(L/'cache-inspection.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),cache=str(cache),listing=str(P),listing_sha256=hashlib.sha256(P.read_bytes()).hexdigest(),records=out),indent=2))
print('prefix objects',len(out),'available',sum('copy' in r for r in out));print(json.dumps(out[:4]))
more=[]
T=B/'lanes/root-edge-irregulator-current-prior-r1/omega-tree.txt'
with T.open() as f:
 for line in f:
  if 'PrefixReversal' not in line:continue
  meta,path=line.rstrip('\n').split('\t',1);mode,typ,oid=meta.split()
  if typ!='blob':continue
  obj=C.c_void_p();rc=g.git_object_lookup(C.byref(obj),repo,C.create_string_buffer(bytes.fromhex(oid)),3)
  r=dict(path=path,sha=oid,lookup_rc=rc)
  if rc==0:
   size=g.git_blob_rawsize(obj);assert size<2000000
   data=C.string_at(g.git_blob_rawcontent(obj),size);g.git_object_free(obj)
   q=L/'prior-bodies-current'/path;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data)
   r.update(copy=str(q.relative_to(L)),sha256=hashlib.sha256(data).hexdigest())
  more.append(r)
(L/'cache-current-inspection.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),snapshot='70af54071bfd4ac098619a9db8c16bb6f7aced11',listing_sha256=hashlib.sha256(T.read_bytes()).hexdigest(),records=more),indent=2))
print('fixed current snapshot',len(more),'available',sum('copy' in r for r in more))
