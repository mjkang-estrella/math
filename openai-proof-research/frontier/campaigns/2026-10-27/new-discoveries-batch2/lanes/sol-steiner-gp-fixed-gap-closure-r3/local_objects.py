import ctypes as C
from pathlib import Path
g=C.CDLL('/usr/lib64/libgit2.so.1.9');g.git_libgit2_init()
repo=C.c_void_p()
g.git_repository_open.argtypes=[C.POINTER(C.c_void_p),C.c_char_p]
assert g.git_repository_open(C.byref(repo),str(Path(__file__).resolve().parent.parent/'root-edge-irregulator-current-prior-r1/omega.git').encode())==0
g.git_tree_lookup.argtypes=[C.POINTER(C.c_void_p),C.c_void_p,C.c_void_p]
g.git_tree_entrycount.argtypes=[C.c_void_p];g.git_tree_entrycount.restype=C.c_size_t
g.git_tree_entry_byindex.argtypes=[C.c_void_p,C.c_size_t];g.git_tree_entry_byindex.restype=C.c_void_p
g.git_tree_entry_name.argtypes=[C.c_void_p];g.git_tree_entry_name.restype=C.c_char_p
g.git_tree_entry_id.argtypes=[C.c_void_p];g.git_tree_entry_id.restype=C.c_void_p
g.git_tree_entry_filemode.argtypes=[C.c_void_p]
g.git_tree_free.argtypes=[C.c_void_p]
def local_tree(s):
 t=C.c_void_p();oid=C.create_string_buffer(bytes.fromhex(s))
 if g.git_tree_lookup(C.byref(t),repo,oid):return None
 out={}
 for i in range(g.git_tree_entrycount(t)):
  e=g.git_tree_entry_byindex(t,i);mode=g.git_tree_entry_filemode(e);p=g.git_tree_entry_name(e).decode();sha=C.string_at(g.git_tree_entry_id(e),20).hex();out[p]={'path':p,'mode':format(mode,'o'),'type':'tree' if mode==16384 else 'blob','sha':sha}
 g.git_tree_free(t);return out
