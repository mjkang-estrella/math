"""Build provenance indexes without changing any upstream/cache bytes.

Run from repository root. Hash coverage is distinct from mathematical reading.
"""
from pathlib import Path
import datetime, hashlib, html, json, re

S = Path('frontier/sources/i28_algebra_discovery')
CACHE = Path('frontier/sources/i14_spectral_width_novelty_r3/corpus')
def sha(b): return hashlib.sha256(b).hexdigest()
def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def save(name, obj): (S/name).write_text(json.dumps(obj, indent=2, ensure_ascii=False)+'\n')
tree = json.loads((S/'inputs/sources/preprints-tree.json').read_text())
manifest = json.loads((S/'inputs/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text())
pinned = json.loads((S/'pinned-manifest.json').read_text())
entries = {e['path']: e for e in tree['tree']}
manuscripts = [e['path'] for e in tree['tree'] if e['type']=='tree' and e['path'].count('/')==1]
assert not tree['truncated'] and len(manuscripts)==749
assert len(manifest['files'])==9340 and manifest['pin']==pinned['pin']
patterns = {
 'direct_subject_words': r'Kurosh|small Cohen|strong Ulam|Cohen--Macaulay|eleven.block',
 'algebra_inventory_titles': r'Kurosh|Cohen|Ulam|Unitariz|Tensor|Spin|Finiteness|Kadison|Kaplansky|Determinant|Bass',
 'involution_lifting': r'involution.{0,60}lift|lift.{0,60}involution',
 'filtered_deformation': r'filtered.{0,40}deform|deform.{0,40}filtered',
}
compiled={k:re.compile(v,re.I) for k,v in patterns.items() if k!='algebra_inventory_titles'}
hits={k:[] for k in compiled}
total=0
for e in manifest['files']:
 b=(CACHE/e['path']).read_bytes()
 assert len(b)==e['bytes'] and sha(b)==e['sha256'] and blob(b)==e['git_blob'], e['path']
 assert entries[e['path']]['sha']==e['git_blob'], e['path']
 total+=len(b)
 txt=b.decode('utf-8')
 for key,pat in compiled.items():
  matched=[i for i,line in enumerate(txt.splitlines(),1) if pat.search(line)]
  if matched: hits[key].append({'path':e['path'],'matching_lines':matched})
save('inventory-audit.json', {
 'audited_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'pin':pinned['pin'],'tree_sha':tree['sha'],'tree_sha256':sha((S/'inputs/sources/preprints-tree.json').read_bytes()),
 'manifest_sha256':sha((S/'inputs/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_bytes()),
 'manuscripts':len(manuscripts),'cache_files_verified':len(manifest['files']),'cache_bytes_verified':total,
 'verification':'Every cache entry: byte length, SHA-256, Git blob SHA-1, and full-tree Git identity. No cache writes or whole-cache copy.',
 'patterns':patterns, 'matches':hits,
 'algebra_inventory_title_matches':[p for p in manuscripts if re.search(patterns['algebra_inventory_titles'],p,re.I)],
 'limits':'Keyword matches locate candidates, not mathematical equivalence. Only selected proofs listed in read-passages were read in full. No absence-of-keyword novelty claim.'})

read=[]; contracts=[]
for e in pinned['files']:
 p=S/'pinned'/e['path']; b=p.read_bytes()
 assert sha(b)==e['sha256'] and blob(b)==e['git_blob'] and entries[e['path']]['sha']==e['git_blob']
 # Read substantive theorem/proof files; do not mislabel bibliography or macros.
 substantive = p.suffix=='.tex' and (p.name in ('paper.tex','surface.tex','strong-ulam-stability.tex') or '/sections/' in str(p))
 if not substantive: continue
 lines=b.splitlines(keepends=True); txt=b.decode()
 read.append({'path':str(p),'start_line':1,'end_line':len(lines),'sha256':sha(b),
   'read_contract':'Complete substantive source/proof file read, not merely theorem extraction. Pinned user-accepted result; new deductions independently checked.'})
 pattern=re.compile(r'\\begin\{(theorem|lemma|proposition|corollary)\}.*?\\end\{\1\}',re.S)
 for match in pattern.finditer(txt):
  statement=match.group(); start=txt[:match.start()].count('\n')+1; end=txt[:match.end()].count('\n')+1
  contracts.append({'path':str(p),'url':e['url'],'git_blob':e['git_blob'],'source_sha256':e['sha256'],
   'environment':match.group(1),'labels':re.findall(r'\\label\{([^}]+)\}',statement),
   'start_line':start,'end_line':end,'passage_sha256':sha(b''.join(lines[start-1:end])), 'exact_statement':statement})

literature_ranges={
 'lubotzky-salomon.txt':[(30,145),(185,376)],
 'anghel-acm.txt':[(1,180),(200,460),(475,600)],
 'anghel-ulrich.txt':[(1072,1120)],
 'chen-local.txt':[(1,160),(245,615)],
 'chen-sun.txt':[(1,150),(180,315),(415,485),(500,610)],
 'bot-v1.txt':[(300,375)],
 'loring.txt':[(50,150)],
 'loring-v4.txt':[(155,385)],
 'knus-sridharan.txt':[(1,60),(530,625)],
 'quasi-gorenstein.txt':[(1,125)],
 'bhm.txt':[(1,120)],
}
for name,ranges in literature_ranges.items():
 p=S/'literature'/name; b=p.read_bytes(); lines=b.splitlines(keepends=True)
 for lo,hi in ranges:
  assert hi<=len(lines),name
  read.append({'path':str(p),'start_line':lo,'end_line':hi,'sha256':sha(b''.join(lines[lo-1:hi])),
   'read_contract':'Exact inspected text range; no claim of entire companion proof coverage beyond these ranges. PDF text is a derivative of the retained version bytes.'})
save('source-contracts.json',{'pin':pinned['pin'],'extraction_note':'Exact theorem environments of the fully read selected substantive source files. Interfaces in report also use surrounding proofs, retained in full. Extraction does not itself certify reading or truth.','contracts':contracts})
save('read-passages.json',{'passage_hash_rule':'SHA-256 of inclusive line slice, preserving newline bytes; line splitting uses bytes.splitlines(keepends=True).',
 'visual_inspection':[{'pdf':'literature/knus-sridharan.pdf','pdf_pages_one_based':[18,19], 'renders':['literature/knus-pages-018.png','literature/knus-pages-019.png'],'purpose':'Check corrupted PDF text glyphs in index/exponent and involution statements; visually inspected both pages.'}],
 'passages':read})
save('search-log.json',{
 'broad_final_round':{'date_utc':'2026-10-09','result_file':'search5.json','tool':'web.run','queries':[
  'algebraic division ring finitely generated involution Kurosh counterexample first kind',
  'filtered deformation small Cohen Macaulay module associated graded nonexistence negative divisor',
  'strong Ulam stability finite local tests amenable almost commuting unitaries operator norm']},
 'targeted_followup':{'date_utc':'2026-10-09','result_file':'search6.json','queries_and_results':'Exact queries retained inside search6.json; led to Lubotzky–Salomon 2607.17578v1, whose Section 2 was read.'},
 'earlier_rounds':{'retained_results':['search2.json','search3.json','search4.json'],
 'provenance_limit':'Exact earlier query strings were not separately recorded. The first exploratory result body was not retained. These limitations are not reconstructed as exact evidence.'},
 'selection_rule':'Only retained primary papers and pinned proofs substantiate mathematical claims. Search snippets, secondary answers, live OpenAI pages and obsolete open-problem status are not source axioms.',
 'scope_limit':'Bounded discovery searches, not an exhaustive bibliography or a priority test.'})
versions=[]
for p in sorted((S/'literature').glob('*-abs.html')):
 raw=p.read_bytes(); txt=html.unescape(re.sub('<[^>]+>',' ',raw.decode()))
 start=txt.index('Submission history'); end=txt.index('Full-text links:',start)
 versions.append({'path':str(p),'source_sha256':sha(raw),'exact_extracted_history':txt[start:end],
 'version_numbers':re.findall(r'\[v(\d+)\]',txt[start:end]),
 'note':'History as retrieved on 2026-10-09; latest checked is maximum displayed version, not a perpetual currentness claim.'})
save('version-history.json',versions)
print(json.dumps({'status':'PASS','manuscripts':len(manuscripts),'cache_files':len(manifest['files']),'cache_bytes':total,'selected_sources':len(pinned['files']),'exact_contracts':len(contracts),'read_ranges':len(read)},indent=2))
