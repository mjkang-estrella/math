from pathlib import Path,PurePosixPath
import hashlib,json,re,urllib.request
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r132')
records=json.loads((R/'artifacts/source-authentication.json').read_text())
t=json.loads(Path('sources/preprints-tree.json').read_bytes())['tree']
lookup={e['path']:e for e in t}
queue=records[:]; seen={x['canonical_path'] for x in records}
while queue:
 rec=queue.pop(0);b=Path(rec['local']).read_text()
 # Only literal mathematical includes and bibliography. No assets/figures downloaded by default.
 refs=re.findall(r'\\(?:input|include)\{([^}]+)\}',b)
 refs += [x+'.bib' for x in re.findall(r'\\bibliography\{([^}]+)\}',b)]
 base=PurePosixPath(rec['canonical_path']).parent
 if '/sections/' in rec['canonical_path']: base=base.parent
 for ref in refs:
  if '#' in ref or '\\' in ref: continue
  if not PurePosixPath(ref).suffix: ref+='.tex'
  p=str(base/ref)
  if p in seen: continue
  e=lookup.get(p) or lookup.get(p.removeprefix('preprints/'))
  if e is None: print('UNRESOLVED',p);continue
  url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+p
  data=urllib.request.urlopen(url,timeout=45).read()
  blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
  assert blob==e['sha'] and len(data)==e['size']
  family='all-dim' if 'every-dimension' in p else 'fourfold'
  dest=R/'private/source'/family/ref;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
  new=dict(canonical_path=p,url=url,size=len(data),git_blob=blob,sha256=hashlib.sha256(data).hexdigest(),local=str(dest))
  records.append(new);seen.add(p);queue.append(new)
  print(family,ref,len(data))
(R/'artifacts/source-authentication.json').write_text(json.dumps(records,indent=2)+'\n')
