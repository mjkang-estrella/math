import pathlib,json,urllib.request,hashlib,re,posixpath
R=pathlib.Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r161'); pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
b=pathlib.Path('sources/preprints-tree.json').read_bytes(); assert hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
t=json.loads(b); es=t['tree'] if isinstance(t,dict) else t; tree={e['path']:e for e in es}
starts=json.loads((R/'private/source/tree-selected.json').read_text()); records=[]; seen=set()
def get(p,base):
 if p in seen:return
 seen.add(p); e=tree[p]; url='https://raw.githubusercontent.com/openai/math/'+pin+'/'+urllib.parse.quote(p,safe='/')
 with urllib.request.urlopen(url,timeout=45) as response: data=response.read(); resolved=response.url
 assert len(data)==e['size']; assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']
 dest=R/'private/source'/p; dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 records.append({'path':p,'size':len(data),'git_blob_sha1':e['sha'],'sha256':hashlib.sha256(data).hexdigest(),'url':url,'resolved_url':resolved})
 print(p,len(data))
 txt=data.decode(); txt=re.sub(r'(?m)(?<!\\)%.*$','',txt)
 for typ,arg in re.findall(r'\\(input|include|bibliography|addbibresource)\s*\{([^}]+)\}',txt):
  for a in arg.split(','):
   ext='.bib' if typ in ['bibliography','addbibresource'] else '.tex'
   a=a.strip(); a=a if a.endswith(ext) else a+ext
   options=[posixpath.normpath(posixpath.join(base,a)),posixpath.normpath(posixpath.join(posixpath.dirname(p),a))]
   q=next((q for q in options if q in tree),None)
   if q is None: print('UNRESOLVED',p,typ,arg); continue
   get(q,base)
for e in starts:get(e['path'],posixpath.dirname(e['path']))
(R/'private/source/authentication.json').write_text(json.dumps(records,indent=2)+'\n')
