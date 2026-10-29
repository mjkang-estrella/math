from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,subprocess
root=Path(__file__).resolve().parent;B=root.parents[1];lanes=root.parent;repo=B.parents[4];review=lanes/'sol-mmpp-primary-body-clearance-r4'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
evidence=json.loads((review/'evidence-hashes.json').read_text())
for n,h in evidence.items():assert sha(review/n)==h,n
frozen=json.loads((lanes/'root-mmpp-survival-review-freeze-r1/review-freeze.json').read_text())['files']
for n,h in frozen.items():assert sha(lanes/'sol-fresh-source-discovery-r90'/n)==h,n
record=dict(utc=datetime.now(timezone.utc).isoformat(),decision='PARK_HISTORICAL_PRIORITY_HOLD',credit=0,counts=[8,38],candidate_files_verified=len(frozen),review_artifacts_verified=len(evidence),math_source='PASS preserved',substantive='PASS preserved with r2 exclusion dissent retained',new_primary='Stover2606.10257v1 full body recovered by worker. Root read actual cached Theorem1.6 and Section2.1 proof passage: separate Poisson-process inclusion, monotone/DCM generator assumptions, no-arrival limiting law v*, not same-process time/Palm comparison. No subsumption supplied by those statements.',stover_sha256=sha(review/'sources/stover.pdf'),root_scope='Read complete r4 report and actual stated primary passages. No complete Stover application/Section4 audit or new mathematical replay claimed.',remaining=['Liu–Neuts1991 pp499–509, including any diagonal-D examples','2026 moment article actual body and conjecture remarks','Cox–Lewis1972 actual interval-law and sinusoidal pages','Exact AMS2024 talk identification and relevant cookbook scope not authenticated'],access='Distinct bounded author/repository/archival routes documented in r4 are exhausted. No repeated blocked publisher/CORE/Euclid/Berkeley requests, credentials, contact, or challenge bypass authorized.',reopen_condition='Genuinely new lawful primary body or source evidence relevant to historical priority. Do not launch repetitive access or eligibility reviews. No Lean/paper until original holds are resolved.',registry='New checkpoint28414a3d55d5b97458b138701407d5678e167a8e at19:30:45; complete d2b0→head9commit4file delta body screen, OpenAI7ef5 unchanged. Inherited chain is bounded, not universal semantic clearance.',review_sha256=sha(review/'review.md'),research='Released slot reassigned to fresh graph/discrete optimization r99; analytic r97 and finite/arithmetic r98 continue.')
(root/'HOLD.json').write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n')
p=B/'NEXT.md';text=p.read_text().replace('Active Sol high/default: MMPP primary-body clearance r4, fresh finite/arithmetic r98, fresh analytic/geometric r97.','Active Sol high/default: fresh graph/discrete optimization r99, fresh finite/arithmetic r98, fresh analytic/geometric r97. MMPP is PARKED at historical-priority HOLD: math/source/substantive PASS retained, r2 dissent preserved; Liu–Neuts1991,2026 moment article and Cox–Lewis bodies remain unread after distinct lawful routes. Stover body is scope-different. No repeated access/eligibility reviews or Lean/paper without genuinely new evidence. See root-mmpp-historical-hold-r5/HOLD.json.')
p.write_text(text)
paths=[p]
for folder in (root,review):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Park MMPP at documented historical body hold and preserve new comparison','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps({'candidate_hashes':len(frozen),'review_hashes':len(evidence),'checks':'PASS','counts':[8,38]}))
