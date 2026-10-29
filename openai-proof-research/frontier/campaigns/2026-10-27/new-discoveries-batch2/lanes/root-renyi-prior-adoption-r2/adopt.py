from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
import json
root=Path(__file__).resolve().parent;lanes=root.parent;B=lanes.parent
review=lanes/'sol-renyi-threshold-current-prior-review-r2'
def digest(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(65536),b''):h.update(b)
    return h.hexdigest()
prov=json.loads((review/'provenance.json').read_text())
for name,d in prov['files'].items():
    p=review/name;assert p.stat().st_size==d['bytes'] and digest(p)==d['sha256'],name
counts={}
for name,manifest in [('sol-fresh-source-discovery-r111','root-renyi-threshold-review-freeze-r1'),('sol-renyi-threshold-preliminary-review-r1','root-renyi-preliminary-adoption-r1')]:
    frozen=json.loads((lanes/manifest/'review-freeze.json').read_text())
    for rel,h in frozen.items():assert digest(lanes/name/rel)==h,rel
    counts[name]=len(frozen)
freeze={str(p.relative_to(review)):digest(p) for p in sorted(review.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc'}
(root/'review-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
record={'utc':datetime.now(timezone.utc).isoformat(),'status':'Historical body screen bounded-clear; combined novelty HOLD for explicit registry coverage gaps','credit':0,'counts':[8,38],
 'root_read':'Completed thread, full review, provenance receipts/coverage fields; independently read actual new citer SectionVII complete proof and SectionVIII-B positive-sum discussion.',
 'new_citer':'Han-Zhan-Zhou-Zhu2610.15716v1,11Oct2026. Theorem5 uses g=f*reflected(f), simplex intersection volume and Gamma quotient. It violates a difference-entropy bound below1; noncentral simplex prevents identification with iid positive-sum density. SectionVIII-B retains Shannon positive-sum conjecture and min-entropy case. No full transfer or target subsumer found.',
 'historical':'Additional actual bodies Li1704.02634, survey1604.04225, Marsiglietti-Melbourne1710.00800 compared by worker; preserved body-specific clearance, not exhaustive priority claim. No identified required inaccessible primary body remains.',
 'recovered_access':'Fresh Omega/OpenAI HEAD and Omega compare HTTP200 with recorded rate headers; old403 are historical, not an ongoing service-block claim.',
 'omega_head':'0a10157da355f1825f38212dd4c2869925ae6785','omega_head_fetch_utc':'2026-10-29T20:58:46.548779Z','omega_commit_utc':'2026-10-29T20:55:08Z','openai_head':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',
 'gaps':['Old compare1b999d9fda71df7537b62327147496d64a6f66ef...2130bf544f7858fc3c142bb9623b7ba9464e22ba has88commits and capped300files','New89cda9...0a10157 delta has72commits241paths,70missing patch bodies enumerated in review registry-audit.json'],
 'next':'Close exact immutable comparison/body gaps; no repeat generic substantive review, no Lean/paper until bounded novelty adjudicated. Newer public counterparts must be compared to candidate sealed proof chronology, not excluded merely for later visibility.',
 'verified_original_paths':counts,'review_provenance_entries_verified':len(prov['files']),'review_paths_frozen':len(freeze),'review_sha256':digest(review/'review.md'),
 'qualifications':['rs PDF extraction font warning; official HTML agrees','Old350009-line tree initially used then corrected to verified350197-line final-freeze baseline','Some combined terminal outputs truncated; exact report and source sections read separately']}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';text=p.read_text()
old='fresh discovery r114 and r115 plus focused Renyi current/historical prior review (all launched; receipts in root-renyi-preliminary-adoption-r1/launch-receipts.json).'
new='fresh discovery r114 and r115; freed prior-review slot reserved for exact Renyi registry-gap closure. Renyi r2 current HEAD requests succeeded (Omega0a10157, OpenAI7ef5); no ongoing access-block claim. New October difference-entropy citer is scope-distinct after actual proof read. Novelty HOLD now identifies capped88-commit historical segment and70missing-body paths. See root-renyi-prior-adoption-r2/ADOPTION.json.'
assert old in text;p.write_text(text.replace(old,new,1))
print(json.dumps({'status':'PASS','frozen_inputs':counts,'review_entries':len(prov['files']),'review_paths':len(freeze)}))
