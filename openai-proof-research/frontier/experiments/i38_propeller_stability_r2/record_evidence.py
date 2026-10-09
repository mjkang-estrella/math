"""One-time creation of review evidence metadata (does not reseal)."""
import hashlib,json
from pathlib import Path
from review_audit import run
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i38_propeller_stability_r2'
A=ROOT/'frontier/sources/i38_inequality_stability_discovery'
C=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def save(name,obj):(S/name).write_text(json.dumps(obj,indent=2)+'\n')
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
pinned=json.loads((A/'pinned-manifest.json').read_text())
selected=[];passages=[]
def passage(path,ranges,interface):
    lines=path.read_bytes().splitlines(keepends=True)
    spans=[]
    for lo,hi in ranges:
        if hi is None:hi=len(lines)
        assert 1<=lo<=hi<=len(lines),(path,lo,hi,len(lines))
        raw=b''.join(lines[lo-1:hi]);spans.append({'start_line':lo,'end_line':hi,'sha256':hashlib.sha256(raw).hexdigest()})
    passages.append({'path':str(path.relative_to(ROOT)),'file_sha256':digest(path),'lines':spans,'interface':interface})
for r in pinned:
    p=r['path'];ranges=None;interface=''
    if 'The-Gaussian-Propeller-Bound' in p and (p.endswith('/main.tex') or any(p.endswith('/'+f+'.tex') for f in ['extremizers','scalars','geometry','elimination','certificates'])):
        ranges=[(1,None)];interface='Entire operative source file; sharp finite maximum, equality, endpoint elimination and certificates.'
    if 'The-symmetric-Mahler-conjecture' in p and p.endswith('/introduction.tex'):
        ranges=[(1,None)];interface='Pinned Hanner equality and limiting functional caveat; secondary screen only.'
    if 'Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring' in p:
        for suffix,rs,why in [('introduction.tex',[(1,None)],'Sharp inequality and equality statement'),('rigidity.tex',[(1,None)],'Entire explicit profile and factorization proof'),('action.tex',[(1,125)],'Auxiliary quantitative remainder statement'),('compactness.tex',[(255,315)],'Fixed rank tail interface')]:
            if p.endswith('/'+suffix):ranges=rs;interface=why+'; secondary screen only.'
    if ranges:
        selected.append(r);passage(C/p,ranges,interface)
assert len(selected)==11,len(selected)
for name,ranges,why in [
 ('hjn-author.txt',[(45,260),(325,1898)],'Theorem1.1, explicit Remark1.4; whole geometric/numerical proof sections2-4 and strict computation interface. Not rerun.'),
 ('hjn-v2.txt',[(70,135)],'Inequality statement and version difference: explicit author uniqueness remark omitted.'),
 ('kn-author.txt',[(1650,1855),(2010,2120)],'Merging, full dimension reduction and planar equality, full Gaussian dual maximum Lemma3.7.'),
 ('hei14-author.txt',[(450,715),(2138,2225)],'Definitions and entire Lemmas2.5-2.8, closing scope discussion.'),
 ('corthree-v3.txt',[(220,285),(975,1560),(2022,2150),(2283,2435),(2660,2735)],'Theorem1.5, Lemmas3.3/4.1 and Cor4.2, circular Lemma6.1, positive eq53 and negative eq65.')]:
    passage(S/'literature'/name,ranges,why)
for name,ranges,why in [('kim-v1.txt',[(82,108),(2169,2208)],'Main theorem and final linear remainder proof; not full paper audit.'),('fgl-v2.txt',[(1,240),(245,380)],'Bubble theorem and parameter scope; not full paper audit.')]:passage(A/'literature'/name,ranges,why)
save('selected-pinned-manifest.json',selected);save('read-passages.json',passages)
versions={}
for name,lo,hi in [('hjn-current.html',169,174),('corthree-current.html',171,178)]:
    path=S/'literature'/name
    versions[name]={'record_lines':'\n'.join(path.read_text().splitlines()[lo-1:hi]),'sha256':digest(path)}
save('versions.json',versions)
save('source-contracts.json',{'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','report':'frontier/reviews/i38-propeller-stability-r2.md','premises':['G sharp finite Gaussian maximum (singular and zero padded included)','G exact extremizer operations; endpoint strictness audited in review Section4','HJN author Theorem1.1 plus explicit Remark1.4, strict tetrahedral proof interface'], 'not_premises':['Numerical stress checks','Heilman quantitative comparisons','Kim or FGL secondary screens','HTTP failure payloads'], 'read_passages':'read-passages.json','primary_responses':'literature/manifest.json','historical_failures':'Original unchanged author evidence and captured verification bind failed 404/403 responses; excluded from proof.', 'coverage':'9340 corpus files mechanically read; 749 manuscript inventory complete, not a claim all full manuscripts were semantically read.', 'rendered_pages':['hjn-author-p3.png','hjn-author-p28.png','hei14-author-p10.png','corthree-v3-p5.png']})
save('corpus-audit.json',run())
print(json.dumps({'selected_pinned_files':len(selected),'read_passage_files':len(passages),'corpus_files':9340}))
