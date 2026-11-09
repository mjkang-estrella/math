"""Read-only verifier. Supply all three detached SHA256 anchors explicitly."""
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath

PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
FAMILY='preprints/The-second-Kahn-Kalai-conjecture-September-24-2026'
ORIGINALS=['frontier/campaigns/2026-10-14/discovery-arithmetic-r162cn-parent/assessment.md']+[
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cn/'+p for p in
 ['private/DERIVATION.md','private/WORKING.md','private/READING-LIMITS.md','FINAL.md']]
DETACHED={'MANIFEST.json','REPORT.json'}
def digest(b):return hashlib.sha256(b).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def safe(s,root=False):
 if root and s=='.':return
 p=PurePosixPath(s)
 need(isinstance(s,str) and s and not p.is_absolute() and '..' not in p.parts and '.' not in p.parts and str(p)==s and '\\' not in s,'unsafe path')
def inventory(root):
 files=[];dirs=[]
 need(stat.S_ISDIR(root.lstat().st_mode),'root must be ordinary directory')
 for base,ds,fs in os.walk(root,followlinks=False):
  b=Path(base); rel=b.relative_to(root).as_posix()
  need(stat.S_ISDIR(b.lstat().st_mode),'nonordinary directory')
  dirs.append({'path':rel,'full_mode':b.lstat().st_mode})
  for name in ds:need(stat.S_ISDIR((b/name).lstat().st_mode),'symlink/special directory')
  for name in fs:
   p=b/name;s=p.relative_to(root).as_posix();safe(s)
   need(stat.S_ISREG(p.lstat().st_mode),'symlink/special file')
   if s in DETACHED:continue
   data=p.read_bytes();files.append({'path':s,'bytes':len(data),'sha256':digest(data),'full_mode':p.lstat().st_mode})
 return sorted(files,key=lambda x:x['path']),sorted(dirs,key=lambda x:x['path'])
def provenance(root):
 tree=json.loads((root/'private/source-tree.json').read_text());auth=json.loads((root/'private/source-authentication.json').read_text())
 need(len(tree)==14 and len(auth)==9,'source cardinalities')
 td={e['path']:e for e in tree};need(len(td)==14 and td[FAMILY]['sha']=='0c319bb1a397494f32fe2b707045e4bb8a064348','source root')
 need(td[FAMILY+'/build/source/main.tex']['sha']=='a4b3c9127c0d1268e18957b11645b54be9f59c69','wrapper anchor')
 need({e['upstream'] for e in auth}=={e['path'] for e in tree if e['type']=='blob'},'source membership')
 for e in auth:
  safe(e['path']); b=(root/e['path']).read_bytes();t=td[e['upstream']]
  need(e['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['upstream'],'pin URL')
  need(len(b)==e['bytes']==t['size'] and digest(b)==e['sha256'],'source size/hash')
  need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==t['sha']==e['git_blob'],'Git blob')
 for d in [e for e in tree if e['type']=='tree']:
  ch=[e for e in tree if str(PurePosixPath(e['path']).parent)==d['path']]
  ch.sort(key=lambda x:PurePosixPath(x['path']).name.encode()+(b'/' if x['type']=='tree' else b''))
  b=b''.join(e['mode'].lstrip('0').encode()+b' '+PurePosixPath(e['path']).name.encode()+b'\0'+bytes.fromhex(e['sha']) for e in ch)
  need(hashlib.sha1(b'tree '+str(len(b)).encode()+b'\0'+b).hexdigest()==d['sha'],'Git tree')
 need(sum(e['bytes'] for e in auth if not e['path'].endswith('.pdf'))==39021,'source text bytes')
 cp=json.loads((root/'private/completed-bindings.json').read_text())
 need([e['original'] for e in cp]==ORIGINALS,'exact completed exceptions')
 project=root.parents[3]
 for e in cp:
  safe(e['copy']); a=project/e['original'];b=root/e['copy'];x=a.read_bytes();y=b.read_bytes()
  need(x==y and len(x)==e['bytes'] and digest(x)==e['sha256'],'original/copy bytes')
  need(a.lstat().st_mode==b.lstat().st_mode==e['full_mode'],'original/copy full modes')
 for e in json.loads((root/'private/primary/bindings.json').read_text()):
  p=root/'private/primary'/(e['name']+'.pdf');b=p.read_bytes()
  need(len(b)==e['bytes'] and digest(b)==e['sha256'] and p.lstat().st_mode==e['full_mode'],'primary PDF binding')
 need(json.loads((root/'private/direct/upstream.json').read_text())['commit']==PIN,'upstream pin')
 return {'source_blobs':9,'source_trees':5,'completed_copies':5,'primary_pdfs':5}
def verify(root,anchors,virtual=None,control=False):
 # virtual is used ONLY for preflight; payload logic is identical before/after seal.
 need(stat.S_ISREG((root/'FINAL.md').lstat().st_mode),'ordinary FINAL file')
 if virtual is None:
  for name in DETACHED:need(stat.S_ISREG((root/name).lstat().st_mode),'ordinary detached file')
 mb,rb=(virtual if virtual is not None else ((root/'MANIFEST.json').read_bytes(),(root/'REPORT.json').read_bytes()))
 need(digest((root/'FINAL.md').read_bytes())==anchors['final'],'FINAL anchor')
 need(digest(mb)==anchors['manifest'],'MANIFEST anchor')
 need(digest(rb)==anchors['report'],'REPORT anchor')
 m=json.loads(mb);r=json.loads(rb)
 need(m['schema']=='r162co-exact-packet-v1','manifest schema')
 need(m['kind']==('control' if control else 'production'),'packet kind')
 paths=[x['path'] for x in m['files']];dpaths=[x['path'] for x in m['directories']]
 need(paths==sorted(set(paths)) and dpaths==sorted(set(dpaths)),'sorted unique membership')
 for p in paths:safe(p);need(p not in DETACHED,'detached payload')
 for p in dpaths:safe(p,True)
 actual,dirs=inventory(root)
 need(actual==m['files'],'exact files/hashes/lengths/FULL modes')
 need(dirs==m['directories'],'exact directories/FULL modes')
 for p in DETACHED:
  if (root/p).exists():need((root/p).lstat().st_mode==m['detached_full_modes'][p],'detached FULL mode')
  else:need(virtual is not None,'missing detached anchor file')
 need(r['final_sha256']==anchors['final'] and r['manifest_sha256']==anchors['manifest'],'report bindings')
 need(r['payload_files']==len(actual) and r['payload_bytes']==sum(x['bytes'] for x in actual) and r['whole_root_files']==len(actual)+2 and r['directories']==len(dirs),'report accounting')
 result={'result':'MATCH','payload_files':len(actual),'payload_bytes':r['payload_bytes'],'whole_root_files':len(actual)+2,'directories':len(dirs),'artifact_only':True}
 if not control:result.update(provenance(root))
 return result
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--final',required=True);p.add_argument('--manifest',required=True);p.add_argument('--report',required=True)
 a=p.parse_args();print(json.dumps(verify(Path(a.root),{'final':a.final,'manifest':a.manifest,'report':a.report}),sort_keys=True))
