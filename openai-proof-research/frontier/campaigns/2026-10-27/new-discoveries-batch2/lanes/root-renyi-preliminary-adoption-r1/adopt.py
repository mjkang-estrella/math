from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
import json
root=Path(__file__).resolve().parent;lanes=root.parent;B=lanes.parent
review=lanes/'sol-renyi-threshold-preliminary-review-r1';candidate=lanes/'sol-fresh-source-discovery-r111'
def digest(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(65536),b''):h.update(b)
    return h.hexdigest()
freeze=json.loads((lanes/'root-renyi-threshold-review-freeze-r1/review-freeze.json').read_text())
for name,h in freeze.items():assert digest(candidate/name)==h,name
rf={str(p.relative_to(review)):digest(p) for p in sorted(review.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc'}
(root/'review-freeze.json').write_text(json.dumps(rf,indent=2)+'\n')
record={'utc':datetime.now(timezone.utc).isoformat(),'status':'SOURCE/MATH/scoped SUBSTANTIVE PASS adopted; NOVELTY HOLD','credit':0,'counts':[8,38],
 'root_read':'Full independent review and completed thread; earlier root normalized-deficit proof/source audit retained. Reviewer independently derives same sign plus sharper fourth-power cofinal bound. No new mathematical defect found.',
 'scope':'Every fixed0<p<1 can beat exponential sum entropy increment with finite truncated-exponential iid log-concave inputs. Hence no proposed p0<1 exists. Shannon p1 and actual optimizer/cube branch untouched.',
 'substantive_adoption':'Source unnumbered assertion has precise expert-attributed quantifiers and intended hypotheses. Closest source majorization fixes h_infinity and bounds output, not normalized increment; difference entropy theorem and pointwise anti-concentration localization do not supply full sum-ratio improvement. Familiar truncation and shortness alone do not establish routine subsumption. New evidence can still overturn eligibility.',
 'prior_review_scope':'Read bodies source3.7/3.4, Melbourne-Tkocz2005.10930 and Melbourne-Tkocz-Wyczesany2406.04200 as documented. Bounded searches/dated registry delta insufficient for current historical closure; no exact subsumer located.',
 'source_evidence':'Official arXivabstract/v3HTML200 independently refreshed and agree with root hashes; reviewer visually inspected actual printedp2. No journal-reference field displayed, no universal nonpublication claim.',
 'validation':'Independent245 interval-overlap cases,99 cofinal arithmetic cases; all61 original candidate paths root-rehashed unchanged. Review sources and receipts sealed by own root manifest; no redundant numerical run.',
 'candidate_paths_verified':len(freeze),'review_paths_frozen':len(rf),'review_sha256':digest(review/'review.md'),
 'provenance_note':'Reviewer delivered separate source/registry/check/freeze receipts but no standalone provenance.json or total manifest. Root binds all delivered files here; no invented reviewer-wide hash verification.',
 'remaining':['Focused current/historical prior-art clearance','Literal unconditional Lean if clearance permits','Manuscript/final review/extracted replay'],
 'action':'Fresh bounded prior-art review, no Lean or paper yet.'}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';text=p.read_text()
text=text.replace('independent Renyi-threshold preliminary review; two freed slots reserved for fresh discovery r114 and r115.','fresh discovery r114; two freed slots reserved for fresh discovery r115 and focused Renyi current/historical prior review.',1)
old='Root normalized-tail/DCT argument and official source comparison pass; independent substantive/novelty review pending, no Lean/paper/credit.'
new='Root adopts independent SOURCE/MATH/scoped SUBSTANTIVE PASS; current/historical novelty HOLD remains. Focused prior review next; no Lean/paper/credit. See root-renyi-preliminary-adoption-r1/ADOPTION.json.'
assert old in text;p.write_text(text.replace(old,new,1))
print(json.dumps({'status':'PASS','candidate_hashes':len(freeze),'review_hashes':len(rf)}))
