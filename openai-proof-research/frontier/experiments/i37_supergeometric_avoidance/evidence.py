"""Build owned reading records once; verify.py never regenerates evidence/seal."""
from pathlib import Path
import hashlib,json,re,html
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i37_supergeometric_avoidance'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(p,v):p.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
reads=[];contracts=[]
def passage(path,first=1,last=None,role='read'):
 p=R/path;b=p.read_bytes();lines=b.decode().splitlines(keepends=True);last=last or len(lines)
 assert 1<=first<=last<=len(lines),(path,first,last,len(lines))
 part=''.join(lines[first-1:last]).encode()
 reads.append(dict(path=path,first_line=first,last_line=last,file_sha256=sha(b),passage_sha256=sha(part),role=role,opening=part.decode()[:180]))
pins=json.loads((S/'pinned-manifest.json').read_text())
for item in pins:
 path=item['local']
 if '/sections/' in path or path.endswith('/main.tex') or path.endswith('/paper.tex'):
  passage(path,role='complete proof section or driver; accepted upstream operations, no truth audit')
  text=(R/path).read_text()
  for match in re.finditer(r'\\begin\{(theorem|lemma|proposition)\}.*?\\end\{\1\}',text,re.S):
   block=match.group(0);label=re.search(r'\\label\{([^}]+)\}',block)
   contracts.append(dict(path=path,label=label.group(1) if label else None,statement=block,sha256=sha(block.encode()),git_blob=item['git_blob'],url=item['url']))
for path in ['AGENTS.md','frontier/iterations/i02-crossfield.md','frontier/reviews/i02-crossfield-r2.md','frontier/iterations/i36-harmonic-analysis-discovery.md','frontier/reviews/i36-common-geometric-avoidance-r2.md','frontier/reviews/i36-common-geometric-avoidance-novelty-r3.md','frontier/findings/R011-rooted-matching-entropy.md']:
 passage(path,role='prior report/rules read; historical conclusions preserved')
passage('frontier/reviews/i25-rooted-entropy-novelty-r3.md',1,85,'decisive combined operation and reduction comparisons')
lit='frontier/sources/i37_supergeometric_avoidance/literature/'
passage(lit+'jiang-v1.txt',role='complete primary proof, including subsequence selection, conditioning, scale estimate, repair, consequences')
for a,b in [(345,742)]:passage(lit+'kp-published.txt',a,b,'published sections 3 and 4')
for a,b in [(285,332),(335,380),(595,625),(712,867)]:passage(lit+'chlebik-v1.txt',a,b,'relative fineness, stronger-universality distinction, center projection, Theorem 15 proof')
passage(lit+'twofold-v2.txt',1,180,'statement/counting interfaces only; not full proof')
passage(lit+'clp-v1.txt',38,72,'Theorem 1.1 and Corollary 1.2, scope')
passage(lit+'clp-v1.txt',674,721,'Proposition 4.4 complete measure-zero proof and stated remaining gap')
passage(lit+'bilipschitz-v1.txt',125,159,'Theorem 1.1 including derivative at zero; statement interface only')
visual=[]
for n in range(3,12):
 path=f'frontier/sources/i36_harmonic_analysis_discovery/literature/kolountzakis-pages/page-{n:02}.png'
 b=(R/path).read_bytes();visual.append(dict(path=path,sha256=sha(b),bytes=len(b),page=n,role='fresh visual read; prior PNG reused; freshly downloaded corrected PDF identical to prior PDF'))
save(S/'read-passages.json',reads);save(S/'visual-read-pages.json',visual);save(S/'source-contracts.json',contracts)
versions=[]
for p in sorted((S/'literature').glob('*current.html')):
 txt=html.unescape(re.sub('<[^>]+>',' ',p.read_text()));pos=txt.find('Submission history');end=txt.find('Full-text links:',pos)
 history=re.sub(r'\s+',' ',txt[pos:end]);versions.append(dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()),submission_history=history))
save(S/'versions.json',versions)
inputs=json.loads((S/'input-manifest.json').read_text());known={x['path'] for x in inputs}
for path in [x['path'] for x in visual]+['frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json','frontier/sources/i36_harmonic_analysis_discovery/literature/retrieval-assessment.json','frontier/sources/i36_harmonic_analysis_discovery/literature/extra-manifest.json','frontier/sources/i36_harmonic_analysis_discovery/literature/manifest.json','frontier/sources/i36_common_geometric_avoidance_novelty_r3/literature/manifest.json']:
 if path not in known:
  b=(R/path).read_bytes();inputs.append(dict(path=path,sha256=sha(b),bytes=len(b),mutable=False));known.add(path)
save(S/'input-manifest.json',inputs)
catalog=(R/'sources/CONTENTS.md').read_text();headings=[x for x in catalog.splitlines() if x.startswith('#')]
families=[dict(number=m.group(1),title=m.group(2)) for m in re.finditer(r'\*\*(\d{3})\.(.*?)\*\*',catalog)]
catalog_manuscripts=sorted(set(re.findall(r'\]\(preprints/([^/]+)/',catalog)))
complete=read_inventory=json.loads((S/'inventory-search.json').read_text())['manuscripts']
save(S/'catalogue-audit.json',dict(sha256=sha(catalog.encode()),heading_count=len(headings),headings=headings,families=families,catalogue_manuscript_paths=catalog_manuscripts,complete_tree_missing_from_catalogue=sorted(set(complete)-set(catalog_manuscripts)),similarity_lines=[dict(line=i,text=line) for i,line in enumerate(catalog.splitlines(),1) if re.search(r'Erd.{0,8}s.{0,30}similarity|geometric.progression',line,re.I)],scope='Complete catalogue parsed; selected similarity entries semantically compared to actual proofs. Catalogue is not complete tree.'))
save(S/'failures-and-limits.json',dict(fresh_http_failures=[],historical_excluded=['wrong guessed Kolountzakis arXiv identifier retrieved Temme; use corrected author PDF','withdrawn 2020 full-similarity claim','old survey status statements superseded by stipulated G/D and current Jiang-Xi'],extraction='1997 PDF text encoding is broken; pages 3-11 visually read from byte-bound prior rendering, whose original PDF matches fresh retrieval.',search='Three saved web query/response objects. Initial exploratory query not retained; not sealed evidence. Search noise is not theorem evidence.',diagnostic_correction='Before sealing, printed min_blocking_cells used Q after a later loop overwrote it from 16 to 512. Exhaustive optimization maxE=2 was unaffected. Corrected output uses literal fixture modulus 16 and asserts result 14.',full_semantic_read_limit='No claim to have semantically read all 749 manuscripts. No full-proof read of CLP, bi-Lipschitz, or twofold paper. No old verifier rerun.'))
print(json.dumps(dict(passages=len(reads),contracts=len(contracts),visual_pages=len(visual),inputs=len(inputs),versions=len(versions))))
