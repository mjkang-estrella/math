#!/usr/bin/env python3
"""Read-only local artifact verifier. Requires detached anchors; no math verdict."""
from pathlib import Path
import argparse,hashlib,json,os,stat,tarfile,io,gzip
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
TREE_SHA='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def digest(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def need(ok,msg):
 if not ok: raise ValueError(msg)
def safe(root,rel):
 p=Path(rel);need(not p.is_absolute() and '..' not in p.parts and str(p)==rel,'unsafe relative path')
 q=root/p;need(q.is_file() and not q.is_symlink(),'missing/nonregular file: '+rel);return q
def same(b,r,what):
 need(len(b)==r['size'] and digest(b)==r['sha256'],'byte identity: '+what)
 if 'gitblob' in r:need(blob(b)==r['gitblob'],'Git blob identity: '+what)
def lfpart(b,a,z):
 lines=b.split(b'\n');return b'\n'.join(lines[a-1:z])+(b'\n' if z<len(lines) else b'')
def inventory(root):
 files={};dirs=[]
 for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for name in ds+fs:
   p=Path(base)/name;st=p.lstat();need(not stat.S_ISLNK(st.st_mode),'symlink: '+str(p))
   if name in ds:need(stat.S_ISDIR(st.st_mode),'not directory');dirs.append(str(p.relative_to(root)))
   else:need(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'nonregular/hardlink: '+str(p));files[str(p.relative_to(root))]=p
 return files,sorted(dirs)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('root',type=Path)
 for n in ['final','manifest','report']:ap.add_argument('--'+n+'-sha',required=True)
 ap.add_argument('--project',type=Path);args=ap.parse_args();root=args.root.resolve()
 for n in ['final','manifest','report']:
  h=getattr(args,n+'_sha');need(len(h)==64 and all(c in '0123456789abcdef' for c in h),'invalid detached anchor')
  need(digest(safe(root,n.upper()+'.md' if n!='manifest' else 'MANIFEST.json').read_bytes())==h,'detached '+n+' anchor')
 m=json.loads((root/'MANIFEST.json').read_bytes());need(m['outside_envelopes']==sorted(ENVELOPES),'envelope policy')
 fs,ds=inventory(root);expected={r['path']:r for r in m['files']}
 need(len(expected)==len(m['files']),'duplicate manifest path')
 need(set(fs)-ENVELOPES==set(expected),'exact payload file membership')
 need(ds==m['directories'],'exact directory membership')
 for rel,r in expected.items():same(safe(root,rel).read_bytes(),r,rel)
 source_count=0;primary_count=0;original_count=0;copy_count=0
 if (root/'source-authentication.json').exists():
  tb=safe(root,'private/preprints-tree.json').read_bytes();need(digest(tb)==TREE_SHA,'complete-tree anchor');t=json.loads(tb)
  need(len(t['tree'])==13223 and t['truncated'] is False,'complete-tree shape');tree={r['path']:r for r in t['tree']}
  for r in json.loads((root/'source-authentication.json').read_bytes()):
   e=tree[r['path']];need(e['type']=='blob' and e['size']==r['size'] and e['sha']==r['gitblob'],'canonical source metadata')
   need(r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path'],'canonical pinned URL')
   same(safe(root,r['local']).read_bytes(),r,r['local']);source_count+=1
 if (root/'primary-authentication.json').exists():
  for r in json.loads((root/'primary-authentication.json').read_bytes()):
   if 'error' in r:continue
   b=safe(root,r['raw']).read_bytes();same(b,r,r['raw'])
   if r['format']=='tar':
    with tarfile.open(fileobj=io.BytesIO(b),mode='r:*') as tf:
     for e in r['members']:
      bb=tf.extractfile(e['name']).read();same(bb,e,e['name']);need(bb==safe(root,e['local']).read_bytes(),'tar selected-copy membership')
   else:
    bb=gzip.decompress(b) if r['format']=='gzip-single' else b;need(len(r['members'])==1,'single-source member count')
    e=r['members'][0];same(bb,e,e['name']);need(bb==safe(root,e['local']).read_bytes(),'single-source membership')
   primary_count+=1
 if (root/'original-authentication.json').exists():
  orig={r['id']:r for r in json.loads((root/'original-authentication.json').read_bytes())}
  copies=json.loads((root/'selected-copy-membership.json').read_bytes())
  for r in copies:
   b=safe(root,r['local']).read_bytes();same(b,r,r['local']);need(r['original_id'] in orig,'unknown original id');copy_count+=1
   if args.project:
    o=orig[r['original_id']];ob=safe(args.project.resolve(),o['path']).read_bytes();same(ob,o,o['path'])
    selected=ob if r['selection']=='whole' else lfpart(ob,*r['lines']);need(selected==b,'original/selected-copy binding')
  if args.project:
   for o in orig.values():same(safe(args.project.resolve(),o['path']).read_bytes(),o,o['path'])
   original_count=len(orig)
 print(json.dumps({'artifact_only':True,'payload_files':len(expected),'outside_envelopes':3,'directories':len(ds),'canonical_sources':source_count,'primary_raw_objects':primary_count,'selected_history_copies':copy_count,'current_originals_checked':original_count,'writes':0},sort_keys=True))
if __name__=='__main__':
 try:main()
 except Exception as e:raise SystemExit('REJECT: '+str(e))
