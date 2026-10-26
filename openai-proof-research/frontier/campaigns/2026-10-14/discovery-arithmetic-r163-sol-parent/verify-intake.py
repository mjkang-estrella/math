from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14'
def sha(a):return hashlib.sha256(a).hexdigest()
def unique(pairs):
 d={}
 for k,v in pairs:assert k not in d;d[k]=v
 return d
def read(p):return json.loads(p.read_bytes(),object_pairs_hook=unique)
def snapshot(root):
 out={}
 for p in root.rglob('*'):
  st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
  if stat.S_ISREG(st.st_mode):
   a=p.read_bytes();out[p.relative_to(root).as_posix()]={'bytes':len(a),'sha256':sha(a),'mode':st.st_mode}
  else:assert stat.S_ISDIR(st.st_mode)
 return out
configs=[('r163-sol','MANIFEST.json','mode',{'FINAL.md':'9380075b2c375a66e5ff9341f68416e9c432b995359791ee2258ec6706c8edd4','MANIFEST.json':'d87fc8a32852e4e8799a555e04b4a29942f74146f1a5d6ed052ba17ee3e49bf5','REPORT.md':'c6e5f81f935f02b936e9870e284519e9e98a8f9a458c64395173cedb0f7fc2a3'}),('r162cu','private/MANIFEST.json','full_mode',{'FINAL.md':'7e9e38cdf6b44365810ae3b67166b5cb45e187a492376dd49ca74b5c78beefd9','private/MANIFEST.json':'899462d568d4cd39fde0297183984c2aebceada13e924189d062a5653afe73af','REPORT.md':'ed923f78ed9f9affd6ab6130a99e4307570b292cde47689d1c5c8973a4e04c92'})]
raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';master=json.loads(raw);assert not master['truncated'];by={e['path']:e for e in master['tree']}
for tag,mname,modekey,anchors in configs:
 R=B/('fresh-arithmetic-discovery-'+tag);D=B/('discovery-arithmetic-'+tag+'-parent');before=read(D/'private/intake/root-before.json');assert snapshot(R)==before
 for n,h in anchors.items():assert before[n]['sha256']==h
 args=['--root',str(R),'--project',str(P)]
 for label,h in zip(['final','manifest','report'],anchors.values()):args+=['--'+label+('-sha256' if tag=='r163-sol' else ''),h]
 run=subprocess.run(['python3','-I','-B',str(R/'verify.py'),*args],cwd=P,text=True,capture_output=True);assert run.returncode==0,(run.stdout,run.stderr)
 m=read(R/mname);names=[e['path'] for e in m['files']];det={mname,'REPORT.md'}|({'ANCHORS.json'} if tag=='r163-sol' else set());assert names==sorted(set(names)) and len(set(n.casefold() for n in names))==len(names) and set(before)==set(names)|det
 for e in m['files']:
  q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path'] and '\\' not in e['path']
  p=R/e['path'];a=p.read_bytes();assert p.stat().st_nlink==1 and len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e[modekey]
 dirs={'.':R.stat().st_mode};dirs.update({p.relative_to(R).as_posix():p.stat().st_mode for p in R.rglob('*') if p.is_dir()});assert dirs=={e['path']:e[modekey] for e in m['directories']}
 if tag=='r163-sol':
  records=read(R/'private/SOURCE-BINDINGS.json');blobrows=[e for e in records if e['type']=='blob'];folders=['preprints/A-power-saving-for-planar-halving-lines-September-25-2026'];copies=read(R/'private/EXCEPTION-BINDINGS.json');primary=read(R/'private/PRIMARY-INVENTORY.json')['items']
 else:
  blobrows=read(R/'private/source-bindings.json')+read(R/'private/companion-bindings.json');folders=sorted({e['path'].split('/build/')[0] if '/build/' in e['path'] else e['path'].rsplit('/',1)[0] for e in blobrows});copies=read(R/'private/exceptions.json');primary=read(R/'private/primary/acquisition.json')+[read(R/'private/primary/fanlott-acquisition.json')]
 selected=[e for e in master['tree'] if any(e['path']==f or e['path'].startswith(f+'/') for f in folders)];assert {e['path'] for e in selected if e['type']=='blob'}=={e['path'] for e in blobrows}
 for e in blobrows:
  source=by[e['path']];p=R/e.get('local',e.get('copy',''));a=p.read_bytes();assert len(a)==source['size'] and sha(a)==e['sha256'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==source['sha']
 trees=0
 for e in selected:
  if e['type']!='tree':continue
  children=[c for c in selected if str(PurePosixPath(c['path']).parent)==e['path']];children.sort(key=lambda c:(PurePosixPath(c['path']).name+('/' if c['type']=='tree' else '')).encode());a=b''.join((c['mode'].lstrip('0')+' '+PurePosixPath(c['path']).name).encode()+b'\0'+bytes.fromhex(c['sha']) for c in children);assert hashlib.sha1(b'tree '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];trees+=1
 for e in copies:
  p=P/e.get('original',e.get('path',''));c=R/e['copy'];a=p.read_bytes();assert a==c.read_bytes() and len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==c.stat().st_mode==e['full_mode']
 for e in primary:
  p=R/e['path'] if 'path' in e else R/'private/primary'/(e.get('name','fanlott')+'.pdf');a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256']
 controls=[]
 for i,n in enumerate(anchors):
  bad=args.copy();bad[5+2*i]='0'*64;r=subprocess.run(['python3','-I','-B',str(R/'verify.py'),*bad],cwd=P,text=True,capture_output=True);assert r.returncode!=0 and 'anchor' in (r.stdout+r.stderr);controls.append(n+' rejected')
 assert snapshot(R)==before
 out={'status':'MATCH','payloads':len(names),'payload_bytes':sum(e['bytes'] for e in m['files']),'whole_files':len(before),'directories':len(dirs),'source_blobs':len(blobrows),'source_trees_independently_verified':trees,'primary_bindings':len(primary),'original_copy_pairs':len(copies),'author_bytes_and_modes_unchanged':True,'controls':controls,'bundled_verifier':run.stdout.strip(),'mathematical_grade':False}
 (D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(tag,json.dumps(out))
