import pathlib,json,hashlib,shutil,re
O=pathlib.Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r125');P=O/'packet'
def H(b):return hashlib.sha256(b).hexdigest()
# Full tree is compact canonical evidence; no repository snapshot.
origins=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/NEW-TEN-2026-10-14.md']
origins += [str(p) for p in sorted(pathlib.Path('frontier/findings').glob('R0*.md')) if 23<=int(p.name[1:4])<=40]
for stem in ['fresh-structural-discovery-r117','fresh-structural-discovery-r124','fresh-analytic-discovery-r123','fresh-arithmetic-discovery-r88']:
 root=pathlib.Path('frontier/campaigns/2026-10-14')/stem
 origins += [str(p) for p in sorted((root/'packet/public').glob('*.md')) if p.name not in ['RIGHTS.md','REPRODUCE.md']]
 origins += [str(p) for p in [root/'REPORT.md',root/'HANDOFF.md'] if p.exists()]
for stem in ['analytic-r123','structural-r124','arithmetic-r88']:
 origins.append('frontier/campaigns/2026-10-14/discovery-'+stem+'-parent/intake.json')
cr=[]
for i,s in enumerate(origins):
 b=pathlib.Path(s).read_bytes(); rel='private/context/'+f'{i:03d}-'+pathlib.Path(s).name;(P/rel).write_bytes(b);cr.append(dict(origin=s,local=rel,bytes=len(b),sha256=H(b)))
(P/'private/context-register.json').write_text(json.dumps(cr,indent=2)+'\n')
hist=[('frontier/campaigns/2026-10-14/fresh-structural-discovery-r113/packet/public/screen-238.md','complete before freeze'),('frontier/iterations/i132-discrete-probability-discovery.md','Candidate T only, AFTER freeze'),('frontier/iterations/i135-complex-analysis-discovery.md','section2.4 permutations only, AFTER freeze'),('frontier/campaigns/2026-10-14/fresh-structural-discovery-r21/checkpoint.md','complete before freeze'),('frontier/campaigns/2026-10-14/fresh-structural-discovery-r21/candidate.md','complete before freeze'),('frontier/iterations/i13-fresh-discovery.md','Section3 actual biregular identity and related common-base passages, partial before freeze'),('frontier/iterations/i29-common-base-entropy.md','actual rank/covariance proof, partial displayed clipping before freeze'),('frontier/campaigns/2026-10-14/fresh-structural-discovery-r35/matching120.md','complete AFTER freeze'),('frontier/campaigns/2026-10-14/fresh-structural-discovery-r122/packet/public/other-screens.md','238 exclusion before freeze')]
hr=[]
for i,(s,extent) in enumerate(hist):
 b=pathlib.Path(s).read_bytes();rel='private/history/'+f'{i:02d}-'+pathlib.Path(s).name;(P/rel).write_bytes(b);hr.append(dict(origin=s,local=rel,bytes=len(b),sha256=H(b),semantic_extent=extent))
(P/'private/history-register.json').write_text(json.dumps(hr,indent=2)+'\n')
# Keep all identities; remove only acquired bodies not used/read.
a=json.loads((P/'private/upstream-register.json').read_text())
for r in a:
 path=r['canonical']['path'];name=path.rsplit('/',1)[-1];ext=''
 if 'Counterexample-to-the-Infinite-Matroid' in path:
  ext={'paper.tex':'wrapper navigation','01-introduction.tex':'complete before freeze','02-matroids.tex':'complete before freeze','06-counterexample.tex':'complete before freeze','07-consequences.tex':'complete before freeze'}.get(name,'')
 elif 'Maximum-Cardinality-Matching' in path: ext={'01-introduction.tex':'complete before freeze','10-f-factors.tex':'complete AFTER freeze'}.get(name,'')
 elif 'Polymatroid' in path:ext={'introduction.tex':'complete before freeze','polyhedra.tex':'227-357, polyhedral-controls proof AFTER freeze'}.get(name,'')
 elif 'Sidorenkos' in path:ext={'complex.tex':'complete before freeze','kernel.tex':'300-455 support and pinning AFTER freeze'}.get(name,'')
 elif 'Conditional-coordinate' in path:ext={'main.tex':'wrapper complete before freeze','01-introduction.tex':'complete before freeze','02-preliminaries.tex':'complete before freeze','03-paths.tex':'complete before freeze','06-induction.tex':'1-160 before freeze; remainder unread','07-analytic.tex':'complete before freeze'}.get(name,'')
 elif 'Compatibility-entropy' in path:ext={'00-introduction.tex':'opening and weighted theorem before freeze; entire introduction reread AFTER freeze','03-spectral-conversion.tex':'complete before freeze'}.get(name,'')
 r['retained']=bool(ext);r['semantic_extent']=ext or 'acquired; no substantive semantic read; removed before seal'
 if not ext:(P/r['local']).unlink()
 else:r['labels_present']=re.findall(r'\\label\{([^}]+)\}',(P/r['local']).read_text())
(P/'private/upstream-register.json').write_text(json.dumps(a,indent=2)+'\n')
for d in sorted((P/'private/upstream').rglob('*'),reverse=True):
 if d.is_dir() and not any(d.iterdir()):d.rmdir()
# Retain locations and limited excerpts, not 15MB of repeated metadata bodies.
f=P/'private/search/history-hits.json';b=f.read_bytes();a=json.loads(b)
for r in a:
 for hit in r['hits']:
  t=hit.pop('text');hit.update(text_sha256=H(t.encode()),text_chars=len(t),excerpt=t[:500],truncated=len(t)>500)
(P/'private/search/history-locations.json').write_text(json.dumps(a,indent=2)+'\n')
(P/'private/search/removed-raw.json').write_text(json.dumps(dict(original_name=f.name,bytes=len(b),sha256=H(b),reason='large mostly metadata lines; locations, hashes and bounded excerpts retained; not raw reconstruction'),indent=2)+'\n');f.unlink()
print({'context':len(cr),'history':len(hr),'canonical':len(json.loads((P/'private/upstream-register.json').read_text()))})
