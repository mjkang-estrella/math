from pathlib import Path
import hashlib,json,re,urllib.request,datetime,concurrent.futures,subprocess
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i37_supergeometric_avoidance'
S.mkdir(parents=True,exist_ok=True)
def sha(b): return hashlib.sha256(b).hexdigest()
def save(name,data): (S/name).write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
inputs=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/TEN-FINDINGS.md','frontier/iterations/README.md','frontier/iterations/i02-crossfield.md','frontier/reviews/i02-crossfield-r2.md','frontier/iterations/i36-harmonic-analysis-discovery.md','frontier/reviews/i36-common-geometric-avoidance-r2.md','frontier/reviews/i36-common-geometric-avoidance-novelty-r3.md','frontier/experiments/i36-r3-parent-verification.json','frontier/sources/i36_harmonic_analysis_discovery/full-brief.txt','frontier/sources/i36_common_geometric_avoidance_r2/full-brief.txt','frontier/sources/i36_common_geometric_avoidance_novelty_r3/full-brief.txt','frontier/sources/i36_harmonic_analysis_discovery/input-manifest.json','frontier/sources/i36_common_geometric_avoidance_novelty_r3/input-manifest.json']
inputs += ['frontier/findings/R011-rooted-matching-entropy.md','frontier/reviews/i25-rooted-entropy-novelty-r3.md']
manifest=[]
for p in sorted(set(inputs)):
 b=(ROOT/p).read_bytes(); mutable=p in ['frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
 dst=S/'frozen'/p; dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
 manifest.append(dict(path=p,sha256=sha(b),bytes=len(b),mutable=mutable,frozen=str(dst.relative_to(ROOT))))
save('input-manifest.json',manifest)
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text()); entries=tree['tree']; bypath={e['path']:e for e in entries}
cache=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
cm=json.loads((cache.parent/'corpus-manifest.json').read_text())
patterns=[r'Erd.{0,8}s.{0,30}similarity',r'super.?lacun|super.?geometr|super.?exponential',r'Chleb|Papageorgiou',r'2\^.*n\^2|n\^\{2\}',r'measure universal|nonuniversality']
audit=[]; pins=[]; total=0
for entry in cm['files']:
 p=entry['path']; b=(cache/p).read_bytes(); total+=len(b)
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert sha(b)==entry['sha256'] and blob==entry['git_blob']
 t=bypath.get(p) or bypath.get(p.removeprefix('preprints/')); assert t and t['sha']==blob
 text=b.decode(); hits=[]
 for i,line in enumerate(text.splitlines(),1):
  matched=[pat for pat in patterns if re.search(pat,line,re.I)]
  if matched: hits.append(dict(line=i,text=line,patterns=matched))
 if hits:audit.append(dict(path=p,sha256=sha(b),hits=hits))
 if '/The-geometric-case-of-the-Erdos-similarity-' in p or '/The-dyadic-case-of-the-Erdos-similarity-' in p:
  pins.append(dict(**entry,local=str((cache/p).relative_to(ROOT))))
save('pinned-manifest.json',pins)
manuscripts=sorted({e['path'].removeprefix('preprints/').split('/')[0] for e in entries if '/' in e['path'].removeprefix('preprints/')})
save('inventory-search.json',dict(entry_count=len(entries),manuscript_count=len(manuscripts),manuscripts=manuscripts,cache_files=len(cm['files']),cache_bytes=total,patterns=patterns,hits=audit))
print(json.dumps(dict(manuscripts=len(manuscripts),cache_files=len(cm['files']),bytes=total,pins=len(pins),hit_files=len(audit))))
