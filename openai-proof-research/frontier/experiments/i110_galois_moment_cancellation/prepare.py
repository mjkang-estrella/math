"""Preparation only. Writes I110 manifests/search; never called by verifier."""
import json,re,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i110_galois_moment_cancellation'
OLD=ROOT/'frontier/sources/i108_galois_tuple_divisibility'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def save(name,obj):(S/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
assert not (S/'seal.json').exists()
refs=set(['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json',
          'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json',
          'frontier/experiments/i108-parent-verification.json'])
for directory in [OLD,ROOT/'frontier/sources/i104_modular_representation_discovery']:
    refs.update(read(directory/'seal.json')['files'])
    refs.update(str((directory/n).relative_to(ROOT)) for n in ['seal.json','seal.sha256'])
refs.update(r['path'] for r in read(OLD/'immutable-references.json'))
A='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/The-Blockwise-Alperin-Weight-Conjecture-September-23-2026/build/sections/'
ID='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Integral-Donovan-Finiteness-over-Witt-Vectors-September-25-2026/build/sections/'
X='frontier/sources/i104_modular_representation_discovery/external/'
passages=[]
def passage(p,start,end,purpose):
    b=(ROOT/p).read_bytes();t=b.decode('utf-8',errors='replace');ls=t.splitlines()
    if end is None:end=len(ls)
    assert 1<=start<=end<=len(ls)
    passages.append({'local':p,'first':start,'last':end,'sha256':sha(b),
        'splitlines_count':len(ls),'lf_split_count':len(t.split('\n')),
        'passage_sha256':sha(('\n'.join(ls[start-1:end])+'\n').encode()),'purpose':purpose})
    if not p.startswith(str(S.relative_to(ROOT))+'/'):refs.add(p)
for file,ranges in [('valuations.tex',[(1,771)]),('specialization.tex',[(1,730)]),
                   ('twist.tex',[(435,462)]),('differentials.tex',[(1,55),(486,782)]),
                   ('group.tex',[(271,382),(608,839)]),('consequences.tex',[(1,171)])]:
    for start,end in ranges:passage(A+file,start,end,'accepted exact source operation, read through its ending')
for file in ['04_comparison.tex','07_assembly.tex']:passage(ID+file,1,None,'complete integral comparison or assembly')
passage(X+'huang-yilmaz-author.pdf.txt',1,None,'complete author manuscript; minimal-field and residual-label distinction')
passage(X+'ffz-blockwise-v2.pdf.txt',56,252,'exact strengthened conjecture and inductive hypotheses')
passage(X+'ffz-blockwise-v2.pdf.txt',1660,2057,'inductive hypotheses and final reduction through final construction; imported triple results attributed')
passage(X+'huang-category-v3.pdf.txt',1095,1149,'central-extension proof through ending; F_p cocycle hypothesis')
passage(X+'huang-category-v3.pdf.txt',1275,1438,'complete compatible-family assembly through ending; earlier category identifications imported')
passage(str((OLD/'external/bby-v1.pdf.txt').relative_to(ROOT)),1,None,'BBY original; complete proof and scope')
passage(str((S/'external/bby-author-20260211.pdf.txt').relative_to(ROOT)),1,None,'later author manuscript, complete proof and ending')
save('passages.json',{'line_convention':'UTF-8 errors=replace; one-based str.splitlines; join selected lines with LF plus one terminal LF','passages':passages})
for p in refs:
    assert not re.search(r'i10[79]|iteration10[79]',p),p
    assert p not in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
save('immutable-references.json',[{'path':p,'sha256':sha((ROOT/p).read_bytes())} for p in sorted(refs)])
q={'domain':'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json',
   'expression':r'Galois.{0,50}(weight|moment|cancell)|Teichm.{0,12}ller|local.point|residue.{0,25}projector|fixed.{0,25}(ordinary|label)|minimal.field',
   'flags':['IGNORECASE'],'line_convention':'UTF-8 errors=replace; str.splitlines one-based; spans zero-based half-open'}
save('query.json',q);pat=re.compile(q['expression'],re.I);hits=[]
for row in read(ROOT/q['domain']):
    for n,line in enumerate((ROOT/row['local']).read_bytes().decode('utf-8',errors='replace').splitlines(),1):
        for m in pat.finditer(line):hits.append({'path':row['path'],'line':n,'span':list(m.span()),'match':m.group(),'text':line})
hits.sort(key=lambda r:(r['path'],r['line'],r['span']))
(S/'search.jsonl').write_text(''.join(json.dumps(r,sort_keys=True,ensure_ascii=False)+'\n' for r in hits))
save('search-summary.json',{'occurrences':len(hits),'families':sorted({r['path'].split('/')[1] for r in hits})})
save('provenance.json',{'original_i110':'task brief bytes copied as UTF-8 without added terminal LF',
    'original_i108_report_sha256':'756db8cd8b2cf97037bc4e5adf343ac8baeb34a18b758a35f170aef286d7596e',
    'original_i108_seal_sha256':'0081d4ceb8f4c724841036d2a16856d89317846a4761006800f5479e4dbbd625',
    'original_parent':'last FINAL PARENT RESPONSE segment of full I110 brief, preserved as text',
    'new_pdfs':['frontier/sources/i110_galois_moment_cancellation/external/bby-author-20260211.pdf'],
    'failures':['Early combined terminal dumps were truncated; relied-on ranges were reread in bounded chunks.',
                'GAP and Sage executable probes returned no path; finite arithmetic implemented in Python.'],
    'unchanged_prerequisite':'I108 original-proof audit of I104; no reopened upstream or I104 truth audit',
    'drift_allowed_live_only':['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']})
print(json.dumps({'references':len(refs),'passages':len(passages),'occurrences':len(hits),'families':len({r['path'].split('/')[1] for r in hits})}))
