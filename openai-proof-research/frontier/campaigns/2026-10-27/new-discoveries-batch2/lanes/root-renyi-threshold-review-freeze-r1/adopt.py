from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
from fractions import Fraction as F
import json,urllib.request
root=Path(__file__).resolve().parent;lanes=root.parent;B=lanes.parent
candidate=lanes/'sol-fresh-source-discovery-r111'
def digest(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(65536),b''):h.update(b)
    return h.hexdigest()
count=0
with (candidate/'manifest.jsonl').open() as f:
    for line in f:
        d=json.loads(line);p=candidate/d['path']
        assert p.stat().st_size==d['bytes'] and digest(p)==d['sha256'],d['path']
        count+=1
freeze={str(p.relative_to(candidate)):digest(p) for p in sorted(candidate.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc'}
(root/'review-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
receipts=[]
for label,url in [('arxiv-abstract','https://arxiv.org/abs/2510.09206'),('arxiv-v3','https://arxiv.org/html/2510.09206v3')]:
    d={'url':url,'utc':datetime.now(timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(url,timeout=25) as response:
            p=root/(label+'.html')
            with p.open('wb') as output:
                for chunk in iter(lambda:response.read(65536),b''):output.write(chunk)
            d.update(status=response.status,final_url=response.url,sha256=digest(p),file=p.name)
    except Exception as error:d.update(error=repr(error),retry=False)
    receipts.append(d)
(root/'primary-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
# Independent rational reduction of the all-n certificate to its worst endpoint.
assert F(1152,8192**2)<F(1,24)
assert F(1,24)+F(1152,8192**2)<F(1,12)<F(1,6)
assert 2*96**2>8192
for n in [2,3,4,7,16,31,64]:
    p=F(n-1,n)
    assert 2/(p*48*n)<=F(1,12*n)<=F(1,24)
record={
 'utc':datetime.now(timezone.utc).isoformat(),'status':'Full ordinary refutation candidate; independent review pending','credit':0,'counts':[8,38],
 'source':'Fu-Li2510.09206v3 printedp2 unnumbered paragraph after(1.2); existential p0 in(0,1) separating exponential/cube-uniform optimizers. Shannon Conjecture1.1 untouched.',
 'root_source_read':'Read retained source definition of log-concavity, entropy, exact threshold paragraph and Lemma3.7; live official arXiv abstract confirms v3 latest21July2026 and official v3HTML inspected. Worker PDF came from mirror; official HTML comparison corroborates statement, not PDF byte authentication.',
 'root_math':'Re-derived normalized ratio ca^p*p*Ja/(1-exp(-pa)), exponential pJ, exact D=J-Ja tail identity. Subadditivity gives bracket<= (2u)^p; MVT gives pointwise0 for fixed0<p<1. Exponential domination enables DCT, hence exp(pa)D ->0<J, giving strict ratio improvement. This settles every fixed subunit order, not p=1. Explicit cofinal n cutoff bounds checked algebraically.',
 'normalization_objection':'Source Lemma3.7 fixes input h_infinity and bounds output alone. It does not compare this increment. Retaining the input factor 1-exp(-pa) is decisive.',
 'root_exact_checks':'All-n certificate reduced to first-term<=1/(12n)<=1/24 and tail<=1152/8192^2<1/24; worst-endpoint rational check plus seven n values. These corroborate universal estimates, not substitute for them.',
 'strongest_eligibility_objection':'Elementary truncation of familiar exponential law may be routine first-variation/classical entropy extremal theory. Need actual published bridge, not inference from shortness. Unnumbered suspected assertion has explicit quantifiers but independent source eligibility remains to adjudicate.',
 'remaining':['Independent adversarial math/source/substantive review','Bounded current semantic prior-art clearance','Literal unconditional Lean endpoint if eligible','Paper and extracted replay if eligible'],
 'manifest_entries_verified':count,'frozen_paths':len(freeze),'proof_sha256':digest(candidate/'PROOF.md'),
 'failures_preserved':['Worker broad optional inventory CPU termination; required selected-text audit finished','CMU404; arXiv alternative legitimate','Initial provisional Maxwell/BNT freshness invalidated by expanded audit'],
 'action':'Independent preliminary review only; no Lean/paper/credit.'}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';text=p.read_text()
text=text.replace('fresh analytic discovery r111 and finite/structural discovery r112; fresh arithmetic/structural discovery r113 (launched; receipt in root-packing-uniform-exclusion-r1/launch-receipt.json).','finite/structural discovery r112 and arithmetic/structural discovery r113; completed r111 replaced by independent Renyi-threshold preliminary review.',1)
marker='r110 Kudra idealizer conjectures remain unresolved;'
insert='r111 supplies a full ordinary refutation candidate of Fu-Li\u2019s existential Renyi threshold below one: truncated exponentials improve the increment for every fixed0<p<1, with explicit cofinal witnesses. Root normalized-tail/DCT argument and official source comparison pass; independent substantive/novelty review pending, no Lean/paper/credit. Shannon Conjecture1.1 untouched. See root-renyi-threshold-review-freeze-r1/ADOPTION.json. '
assert marker in text;text=text.replace(marker,insert+marker,1);p.write_text(text)
print(json.dumps({'status':'PASS','manifest_entries':count,'frozen_paths':len(freeze),'primary_receipts':receipts}))
