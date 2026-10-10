"""I95 historical capture only. Writes only owned evidence. NOT a verifier."""
import sys
sys.dont_write_bytecode=True
from evidence import *
def save(p,x):path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
assert not path(EX[0]).exists()
# Preserve initial four snapshots; AGENTS is also immutable.
path(S+'/snapshots/AGENTS.md').write_bytes(raw('AGENTS.md'))
inputs=[]
for p in sorted(MUTABLE+['AGENTS.md']):
    snap=S+'/snapshots/'+p.replace('/','__')
    inputs.append({'path':p,'snapshot':snap,'sha256':sha(raw(snap)),'mutable':p in MUTABLE})
save(S+'/inputs.json',inputs)
refs={}
for lane in ['i89_geometric_group_discovery','i91_finite_cat0_obstruction']:
    base='frontier/sources/'+lane
    files=load(base+'/seal-v1.json')['files']
    if isinstance(files,dict):files=[{'path':p,**v} if isinstance(v,dict) else {'path':p,'sha256':v} for p,v in files.items()]
    for d in files+load(base+'/immutable-references.json'):
        assert sha(raw(d['path']))==d['sha256']
        if d['path'] in refs:assert refs[d['path']]==d['sha256']
        refs[d['path']]=d['sha256']
    for p in [base+'/seal-v1.json',base+'/seal-v1.sha256',base+'/immutable-references.json']:refs[p]=sha(raw(p))
for p in ['frontier/experiments/i91-parent-verification.json','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/seal-v1.json']:
    refs[p]=sha(raw(p))
assert not any('i94_' in p or 'i96_' in p for p in refs)
save(S+'/immutable-references.json',[{'path':p,'sha256':h} for p,h in sorted(refs.items())])
# Reads record actual bounded passages, not an assertion that hashes imply reading.
reads=[]
def readrecord(p,start,end,scope):
    b=raw(p);ls=b.decode().splitlines(keepends=True)
    if '/primary/' in p and end is not None:
        # Reads were displayed by sed (LF lines); PDF formfeeds also split Python lines.
        nl=b.decode().split('\n');prefix='\n'.join(nl[:start-1])+('\n' if start>1 else '')
        selected='\n'.join(nl[start-1:end])+('\n' if end<len(nl) else '')
        start=len(prefix.splitlines(keepends=True))+1;end=start+len(selected.splitlines(keepends=True))-1
    if end is None:end=len(ls)
    assert 1<=start<=end<=len(ls)
    text=''.join(ls[start-1:end])
    reads.append({'path':p,'start':start,'end':end,'scope':scope,'labels':re.findall(r'\\label\{([^}]+)\}',text),'source_sha256':sha(b),'passage_sha256':sha(text.encode()),'line_convention':'str.splitlines(keepends=True)'})
A='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/build/sections/'
for p in sorted(path(A.rstrip('/')).glob('*.tex')):readrecord(p.relative_to(R).as_posix(),1,None,'COMPLETE operative source section; source truth stipulated, applicability audited')
readrecord('frontier/iterations/i91-finite-cat0-obstruction.md',1,None,'COMPLETE original I91 report')
readrecord('frontier/iterations/i89-geometric-group-discovery.md',75,218,'COMPLETE scoped I89 F89/Lemmas3.1/3.2/finite estimates/tree and comparison; R89/H89/E89 excluded')
for p in ['template.py','algebraic.py','checks.py','verify.py']:
    readrecord('frontier/experiments/i91_finite_cat0_obstruction/'+p,1,None,'COMPLETE original I91 implementation')
for p,start,end,scope in [('gromov.txt',1970,2172,'Complete operative §§3.8.B–D comparison, through final remark'),('kondo.txt',348,445,'Complete §6 fixed-point openness and halving proofs'),('ikn.txt',230,310,'Energy normalization, Proposition2.1 and complete following argument'),('ikn.txt',648,682,'Proposition2.8 and Theorem2.9 with complete proofs')]:
    readrecord('frontier/sources/i89_geometric_group_discovery/primary/'+p,start,end,scope)
readrecord('frontier/sources/i91_finite_cat0_obstruction/primary/berg-nikolaev.txt',1,178,'Primary v1: zero-curvature formula, both orientations and contrast with K!=0 theorem')
C='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
art=C+'An-Artin-group-with-no-geometric-CAT-0-action-September-23-2026/build/sections/'
for name,start,end in [('introduction.tex',55,100),('lengths.tex',1,251),('sectors.tex',231,327),('assembly.tex',298,425)]:readrecord(art+name,start,end,'Scoped companion applicability comparison; no independent truth or novelty verdict')
fill=C+'Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/build/sections/'
readrecord(fill+'01-introduction.tex',1,80,'Proper CAT(0) current-filling hypotheses')
readrecord(fill+'07-conclusion.tex',1,169,'Complete opposite-average/variance operation')
readrecord(C+'Generalized-Cartan-Hadamard-isoperimetry-and-Euclidean-equality-rigidity-September-23-2026/build/sections/01-introduction.tex',1,89,'Exact main and equality statements, through qualification')
save(S+'/readings.json',sorted(reads,key=lambda d:(d['path'],d['start'],d['end'])))
# Replay author's complete lexical searches independently, plus one new bounded-expression screen.
qs=load('frontier/sources/i91_finite_cat0_obstruction/searches.json')
new={'name':'i95_metric_certificates','pattern':r'Reshetnyak|quasilineariz|reverse[- ]median|finite.{0,25}CAT','output':S+'/metric-certificate-search.json'}
allq=qs+[new];records,hits,corpus=complete_domain(allq)
for q,h in zip(qs,hits):assert load(q['output'])==h and q['count']==len(h)
new['count']=len(hits[-1]);save(new['output'],hits[-1]);save(S+'/searches.json',allq)
save(S+'/body-inventory.json',records)
path(S+'/corpus-rg-files.txt').write_text('\n'.join(corpus)+'\n')
# Re-extract only these selected PDFs during verification, not all 776.
pdfs=[]
outside=[json.loads(l) for l in raw('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').splitlines()]
for d in outside:
    if d['path'].startswith('preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/') and d['path'].endswith('/paper.pdf'):
        pdfs.append({'pdf':d['local'],'text':d['extraction']['path']})
for stem in ['gromov','kondo','ikn']:pdfs.append({'pdf':'frontier/sources/i89_geometric_group_discovery/primary/'+stem+'.pdf','text':'frontier/sources/i89_geometric_group_discovery/primary/'+stem+'.txt'})
pdfs.append({'pdf':'frontier/sources/i91_finite_cat0_obstruction/primary/berg-nikolaev.pdf','text':'frontier/sources/i91_finite_cat0_obstruction/primary/berg-nikolaev.txt'})
for d in pdfs:d.update(pdf_sha256=sha(raw(d['pdf'])),text_sha256=sha(raw(d['text'])))
save(S+'/selected-pdf-replays.json',sorted(pdfs,key=lambda d:d['pdf']))
print(json.dumps({'references':len(refs),'readings':len(reads),'body_records':len(records),'search_hits':{q['name']:len(h) for q,h in zip(allq,hits)},'selected_PDFs':len(pdfs)},sort_keys=True))
