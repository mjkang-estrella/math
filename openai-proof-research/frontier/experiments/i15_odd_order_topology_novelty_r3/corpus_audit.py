from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i15_odd_order_topology_novelty_r3'
C=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
m=json.loads((C.parent/'corpus-manifest.json').read_text())
t=json.loads((ROOT/'sources/preprints-tree.json').read_text()); tree={x['path']:x for x in t['tree']}
assert not t.get('truncated'); assert len(tree)==len(t['tree'])
patterns={
'exact_order':r'(order[\s~-]*(three|3)|three[\s~-]*(fold|sheet)|ternary|six[\s~-]*tip|odd[\s~-]*(order|prime))',
'realization':r'(Nielsen|non[ -]?reali[sz]|unreali[sz]|homeomorphism|manifold model|outer automorphism)',
'arity':r'(arbitrary|general|any|finite)[^\n.]{0,90}(grope|cap|law|arity|commutator|marked bod|tip)',
'geometry':r'(marked bod|tip annul|grope|cyclic.cover|reflection)',
}
rx={k:re.compile(v,re.I) for k,v in patterns.items()}; hits={k:[] for k in patterns}; dirs=set(); size=0
for f in m['files']:
 b=(C/f['path']).read_bytes();assert len(b)==f['bytes'];assert hashlib.sha256(b).hexdigest()==f['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==f['git_blob']==tree[f['path']]['sha']
 size+=len(b);dirs.add(f['path'].split('/')[1]);text=b.decode(errors='replace')
 for k,r in rx.items():
  for match in r.finditer(text):
   a=max(0,match.start()-150);z=min(len(text),match.end()+220)
   hits[k].append({'path':f['path'],'line':text[:match.start()].count('\n')+1,'context':text[a:z]})
for k,v in hits.items():(S/('corpus-'+k+'-hits.json')).write_text(json.dumps(v,indent=2)+'\n')
co=[]
for d in sorted(dirs):
 dh={k:[x for x in v if x['path'].split('/')[1]==d] for k,v in hits.items()}
 if dh['realization'] and (dh['geometry'] or dh['exact_order']):co.append({'manuscript':d,'counts':{k:len(v) for k,v in dh.items()}})
result={'pin':m['pin'],'files_verified':len(m['files']),'bytes':size,'manuscripts':len(dirs),'tree_entries':len(tree),'tree_blobs':sum(v['type']=='blob' for v in tree.values()),'patterns':patterns,'counts':{k:len(v) for k,v in hits.items()},'cooccurrence_manuscripts':co,'limits':'Full corpus text screen, not exhaustive semantic reading. Retained cache was read only.'}
(S/'corpus-audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
