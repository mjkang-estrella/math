from pathlib import Path
import json,hashlib,re
root=Path(__file__).resolve().parents[3];s=root/'frontier/sources/i25_rooted_entropy_novelty_r3';cache=root/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
manifest=json.loads((cache.parent/'corpus-manifest.json').read_text())
patterns={'matching-entropy':r'(?is)(perfect.match|hafnian|bethe).{0,180}(entropy|entrop|lower.bound)|(entropy|entrop).{0,180}(perfect.match|hafnian|bethe)','root-reserve':r'(?is)(root|star).{0,90}(entropy|reserve)|(entropy|reserve).{0,90}(root|star)','tight-entropy':r'(?is)tight.{0,20}cut.{0,180}entrop|entrop.{0,180}tight.{0,20}cut'}
hits={k:[] for k in patterns};bad=[]
for r in manifest['files']:
 p=cache/r['path'];b=p.read_bytes()
 if hashlib.sha256(b).hexdigest()!=r['sha256']:bad.append(r['path'])
 t=b.decode(errors='replace')
 for k,pat in patterns.items():
  mm=list(re.finditer(pat,t))
  if mm:hits[k].append(dict(path=r['path'],matches=len(mm),snippets=[m.group(0)[:400] for m in mm[:6]]))
tree=json.loads((root/'sources/preprints-tree.json').read_text())['tree'];dirs=sorted({r['path'].split('/')[1] for r in tree if r['path'].startswith('preprints/')})
(s/'corpus-search.json').write_text(json.dumps(dict(files_verified=len(manifest['files']),bad=bad,manuscripts=len(dirs),patterns=patterns,hits=hits),indent=2)+'\n')
print('verified',len(manifest['files']),'manuscripts',len(dirs),'bad',len(bad))
for k,v in hits.items():print(k,len(v));print('\n'.join(x['path'] for x in v if ('Matching' in x['path'] or 'Entropy' in x['path']) )[:6000])
