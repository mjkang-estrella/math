"""One-time evidence preparation; NOT part of the offline verifier.
Writes only the three I128 owned paths. Never edits inherited bytes or seals.
"""
from pathlib import Path
import json,hashlib,re,runpy
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i128_statistical_learning_discovery'
E=ROOT/'frontier/experiments/i128_statistical_learning_discovery'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def rel(p):return str(p.relative_to(ROOT))
def sha(b):return hashlib.sha256(b).hexdigest()
def row(p):
    b=p.read_bytes();return {'path':rel(p),'bytes':len(b),'sha256':sha(b)}
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def prepare():
    assert not (S/'seal.json').exists(),'do not prepare after sealing'
    domain=json.loads((ROOT/'frontier/sources/i113_online_optimization_discovery/search-domain.json').read_text())
    corpus=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints'
    passages=[]
    def add(p,start=1,end=None,convention='splitlines',scope='read'):
        if not p.is_absolute():p=ROOT/p
        text=p.read_bytes().decode('utf8',errors='replace');ls=text.splitlines() if convention=='splitlines' else text.split('\n')
        if end is None:end=len(ls)
        assert 1<=start<=end<=len(ls),(p,start,end,len(ls))
        d=row(p);d.update(start=start,end=end,total_lines=len(ls),line_convention=convention,passage_sha256=sha('\n'.join(ls[start-1:end]).encode()),scope=scope)
        for r in domain:
            if r['local']==rel(p):d['source_path']=r['path'];d['url']='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path'];break
        passages.append(d)
    def cp(pattern,start=1,end=None):add(next(corpus.glob(pattern)),start,end)
    for p in sorted(S.glob('decoded-*.txt')):add(p,scope='complete decoded recursive fields; duplicate escaped replay strings are byte-bound, not separate mathematical readings')
    add(Path('AGENTS.md'));add(Path('sources/upstream.json'))
    for s,e in [(2920,2950),(2977,3010),(3334,3413)]:add(Path('sources/CONTENTS.md'),s,e)
    add(Path('frontier/iterations/i125-dini-singular-packing.md'))
    add(Path('frontier/experiments/i125-parent-verification.json'),scope='final original parent response also supplied in brief')
    add(Path('frontier/experiments/i125-parent-order-replay.py'))
    add(Path('frontier/experiments/i125_dini_singular_packing/verify.py'))
    add(Path('frontier/sources/i125_dini_singular_packing/external/dss-v1.txt'),640,843,'LF')
    add(Path('frontier/sources/i125_dini_singular_packing/external/det-v2.txt'),2326,2585,'LF')
    for name in ['main.tex','sections/flow.tex','sections/scalar.tex','sections/capacity.tex','sections/canonical.tex','sections/reserve.tex','sections/thinning.tex','sections/upgrade.tex','references.bib']:
        cp('Sharp-binary*/build/'+name)
    cp('Hellinger*/build/main.tex')
    for name in ['main.tex','setup.tex','decoding.tex','separation.tex']:cp('Uniform-quasipolynomial*/build/manuscript/'+name)
    for name in ['main.tex','summary.tex','part-1.tex']:cp('A-latest-anchor*/build/'+name)
    for p in sorted(corpus.glob('Average-Sensitivity*/build/sections/*.tex')):add(p)
    for name in ['introduction.tex','sampling.tex']:cp('Subpolynomial*/build/sections/'+name)
    for name in ['introduction.tex','streaming.tex','endpoint.tex']:cp('Memory-and-precision*/build/sections/'+name)
    cp('Memory-and-precision*/build/sections/density-variants.tex',1,364)
    cp('Replacing-Gaussian*/build/sections/00-introduction.tex')
    cp('Posterior-replicas*/build/sections/00-introduction.tex')
    for pat,end in [('i38-*',65),('i53-*',65),('i59-*',110),('i61-*',55),('i114-*',65),('i120-*',65),('i123-*',70)]:
        add(next((ROOT/'frontier/iterations').glob(pat)),1,end,scope='scoped overlap; not full-report re-audit')
    add(ROOT/'frontier/findings/R009-variable-channel-capacity.md')
    for pat,end in [('R012*',90),('R014*',85)]:
        p=next((ROOT/'frontier/findings').glob(pat));add(p,1,min(end,len(p.read_text().splitlines())),scope='scoped overlap')
    add(S/'external/ky-stability-html.txt')
    add(S/'external/chen-proof-html.txt',2540,2670,scope='complete relevant §9 induction and semigroup ending; external Bellman/certificates not re-proved')
    dump(S/'read-manifest.json',{'passages':passages,'limits':'Full bytes and exact ranges are evidence of reading scope, not universal proof certification; no claim of semantic coverage of all corpus.'})
    references={d['path']:row(ROOT/d['path']) for d in passages if not d['path'].startswith(rel(S)+'/') and d['path'] not in {'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}}
    dump(S/'reading-references.json',[references[p] for p in sorted(references)])
    contracts=[]
    for d in passages:
        if 'source_path' not in d:continue
        ls=(ROOT/d['path']).read_text().splitlines()
        for i in range(d['start'],d['end']+1):
            for m in re.finditer(r'\\label\{[^}]+\}',ls[i-1]):contracts.append({'path':d['path'],'line':i,'needle':m.group(),'text':ls[i-1]})
    dump(S/'source-contracts.json',contracts)
    expression=r'fixed.information|randomiz|stability|Markov|uniform|bit.complex|terminal|fresh|precision|between.query'
    paths=sorted({d['path'] for d in passages if 'source_path' in d});hits=[]
    for p in paths:
        for i,line in enumerate((ROOT/p).read_text().splitlines(),1):
            ms=list(re.finditer(expression,line,re.I))
            if ms:hits.append({'path':p,'line':i,'text':line,'occurrences':[{'start':m.start(),'end':m.end(),'text':m.group()} for m in ms]})
    dump(S/'focused-lexical.json',{'expression':expression,'paths':paths,'hits':hits,'scope':'selected exact-source strings only, not semantic absence'})
    lex=[];pattern=r'R009|R012|R014|I38|I5[3-9]|I61|I11[3-9]|I12[0-5]|eight|8/10'
    for d in json.loads((S/'snapshots.json').read_text()):
        if not d['drift']:continue
        for i,line in enumerate((ROOT/d['snapshot']).read_text().splitlines(),1):
            mm=list(re.finditer(pattern,line,re.I))
            if mm:lex.append({'snapshot':d['snapshot'],'line':i,'text':line,'occurrences':[{'start':m.start(),'end':m.end(),'text':m.group()} for m in mm]})
    dump(S/'ledger-overlap.json',{'expression':pattern,'hits':lex,'scope':'lexical scan of frozen ledgers; prior actual hypotheses read separately'})
    inherited={}
    for name in ['i113_online_optimization_discovery','i116_robust_prophet_continuation','i119_one_loss_online_selection','i122_variational_free_boundary_discovery','i125_dini_singular_packing']:
        sp=ROOT/'frontier/sources'/name/'seal.json';seal=json.loads(sp.read_text())
        for d in seal['files']:
            p=d['path'];assert p not in inherited or inherited[p]==d;inherited[p]=d
        inherited[rel(sp)]=row(sp)
    for name in ['i113','i116','i119','i122','i125']:
        p=ROOT/'frontier/experiments'/f'{name}-parent-verification.json';inherited[rel(p)]=row(p)
    p=ROOT/'frontier/experiments/i125-parent-order-replay.py';inherited[rel(p)]=row(p)
    dump(S/'inherited-references.json',[inherited[p] for p in sorted(inherited)])
    ext=json.loads((S/'external-manifest.json').read_text())
    for d in ext:
        if d['path'].endswith('-abs.html'):d['versions']=re.findall(r'\[v[0-9]+\]',(ROOT/d['path']).read_text())
    dump(S/'external-manifest.json',ext)
    dump(E/'diagnostics.json',runpy.run_path(str(E/'diagnostics.py'))['run']())
    dump(S/'history.json',{
      'original_failure':'Original I125 verifier exit 1: ValueError: canonical inventory. See original-evidence-audit.json; never repaired.',
      'preserved_argument_limits':['I122 general-Lambda logarithmic equality FAIL; corrected primitive separate','S128 global coordinate selection unpaid','local Linfinity entrance fails for admissible rare spikes','Boolean seed lift changes initial information and noise observation','Markov full-retention decoder exponential only','sampling query count is not bit runtime','noise simulation is a paid source operation'],
      'failed_or_truncated_reads':[
        'Initial broad ledger/source reads exceeded tool output caps; only separately displayed ranges and scoped ledger matches claimed.',
        'cat frontier/experiments/i125_dini_singular_packing/evidence.py failed: nonexistent file; correct verifier later read.',
        'A selected-inventory read used the parent math cwd and failed FileNotFoundError; rerun with repository workdir.',
        'Combined decoded I122/I119 displays truncated; split ranges reread. Duplicate JSON escaped stdout is also parsed/bound, not claimed as an additional mathematical reading.',
        'Combined web search and separation/density display truncated; separation reread 1-280 and 281-548, density displayed full 1-364.',
        'Broad I38/I53/I60/I61/I117/I120 display truncated; report claims only recorded overlap ranges, not full reviews.',
        'Glob i55-* raised StopIteration: I55/I56 are inherited review records. No missing iteration file manufactured.',
        'Combined ledger and regression-companion display truncated; Replacing introduction reread 1-140 and 141-ending; Posterior introduction displayed through ending.',
        'An accidental Object.keys on a stored search string produced truncated character indices; no mathematical evidence inferred.'
        ,'Latest-anchor part-1 lines 106-310 display truncated a scalar table; lines 210-240 were reread, with 1-105 and 311-488 completing the source through its ending.'
      ],
      'retrievals':'Four arXiv HTML/version downloads returned HTTP 200. A later direct BBS primary-page web open returned Checking your browser - reCAPTCHA, frozen in external/bbs-web-open.txt; not treated as a completed paper retrieval. No new PDF extraction. Web searches are discovery evidence only.',
      'html_convention':'HTMLParser text views replace math elements with alttext, suppress scripts/styles, collapse whitespace within nonempty block lines, UTF8 LF. Original HTML and text hashes both retained. No claim that HTML is PDF-identical.',
      'source_limits':'Sharp binary source all operative sections and PTF all proof/consequence sections read. Hellinger introduction contract only. Trace latest-anchor companion, separation/decoder read through endings; no new theorem assumes extension of their multiscale antecedents. Regression/sampling selected exact model and terminal operations read, not all companion proofs.',
      'semantic_limits':'Search strings and manuscript title selection do not certify semantic corpus coverage or worldwide priority.'})
    print(json.dumps({'passages':len(passages),'source_contracts':len(contracts),'lexical_lines':len(hits),'inherited_references':len(inherited)},sort_keys=True))

if __name__=='__main__':prepare()
