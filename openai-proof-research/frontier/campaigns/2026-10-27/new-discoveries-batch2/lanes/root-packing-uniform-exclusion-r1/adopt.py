from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
import json
root=Path(__file__).resolve().parent;lanes=root.parent;B=lanes.parent
candidate=lanes/'sol-fresh-source-discovery-r108'
review=lanes/'sol-packing-uniform-eligibility-review-r1'
def digest(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(65536),b''):h.update(b)
    return h.hexdigest()
freeze=json.loads((lanes/'root-fresh-source-r108-r109-handbacks/r108-freeze.json').read_text())
for name,h in freeze.items():
    assert digest(candidate/name)==h,name
    assert digest(review/'inputs/r108'/name)==h,name
entries=0
for line in (review/'review-artifacts.sha256').read_text().splitlines():
    h,name=line.split(maxsplit=1)
    assert digest(review/name.lstrip('*'))==h,name
    entries+=1
record={
 'utc':datetime.now(timezone.utc).isoformat(),'decision':'EXCLUDE_ROUTINE_SOURCE_ADAPTATION','credit':0,'counts':[8,38],
 'claim':'Blitvic-Kammoun-Steingrimsson2610.29846v1 Section7 item6, uniform representatives for all integers m>2,K>2m with prescribed j-packing counts (2j-1)!! for every j>=1',
 'source':'PASS','ordinary_math':'PASS','substantive':'FAIL','historical_novelty':'HOLD; no exact earlier representative located',
 'root_basis':'Root read full independent review and provenance, previously full candidate proof and actual source Prop5.24 proof; additionally inspected source neutral-chain passages around lines3921-3927 and4269-4278. Both closure inclusions and all boundary cases survive.',
 'complete_exclusion_bridge':'The literal pattern realizes the source core with one unit leaf at each attachment. Removing globally comparable initial chain leaves the same comb for every (m,r), r=K-2m-1. Raising r only inserts j chain vertices; raising m at fixed r inserts j+1. These preserve linear-extension counts by the source explicitly stated neutral-element operation. Prop5.24 applies on these exact objects with branch length1 and off-branch upper counts0,2,...,2j-2; its product is (2j-1)!!. Remaining construction is the local compatible ordering of those neutral vertices, a routine source adaptation.',
 'strongest_countercase':'This really answers the full explicit open representative question. Prop5.24 alone does not existentially produce the word; no claim that the exact endpoint was already published. Exclusion is based on the direct source comb realization and count-neutral parameter padding, not shortness or absence of a novel counting theorem.',
 'validation':'Root prior60 literal closure/hook cases; independent144 closure comparisons and20 exhaustive residual-permutation counts pass. Universal argument is symbolic, not finite extrapolation. No redundant checker replay needed after unchanged hashes.',
 'frozen_original_and_review_copy_paths':len(freeze),'review_manifest_entries':entries,'review_sha256':digest(review/'review.md'),
 'remaining':'Source items5 and8 unresolved. No full classification or cutoff claim.',
 'limitations':['Current semantic registry absence unestablished','Earlier300-file comparison truncation retained','Reviewer initial bounded read-only shell calls unguarded, disclosed; no write or cap increase','RSS guard samples cannot exclude sub-sample spikes'],
 'action':'Stop Lean/paper investment for this candidate. Preserve full ordinary proof and independent dissent argument. No ledger/count/public changes.'}
(root/'EXCLUSION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';text=p.read_text()
text=text.replace('independent packing-construction eligibility review; fresh analytic discovery r111 and finite/structural discovery r112 (all three launched; receipts in root-fresh-source-r110-handback/launch-receipts.json).','fresh analytic discovery r111 and finite/structural discovery r112; freed review slot reserved for fresh arithmetic/structural discovery r113.',1)
old='r108 full uniform double-factorial packing construction passes root ordinary checks, but routine-source-adaptation exclusion awaits independent adjudication.'
new='r108 full uniform double-factorial packing construction is ordinary-math PASS but EXCLUDED from discovery credit after independent review and root primary-body comparison: exact source comb with count-neutral chain padding, then Prop5.24. This is not a claim of a printed exact prior representative; novelty HOLD remains. See root-packing-uniform-exclusion-r1/EXCLUSION.json. No Lean/paper investment.'
assert old in text;text=text.replace(old,new,1);p.write_text(text)
print(json.dumps({'status':'PASS','original_and_copy_paths':len(freeze),'review_manifest_entries':entries,'credit':0}))
