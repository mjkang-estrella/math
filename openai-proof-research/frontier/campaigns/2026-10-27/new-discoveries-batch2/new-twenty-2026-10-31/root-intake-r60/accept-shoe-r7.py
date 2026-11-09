import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,zipfile,shutil,collections
P=Path(__file__).resolve().parent.parent;R=P/'shoe-pair-discrepancy-formal-independent-review-sol-r6';F=P/'shoe-discrepancy-root-final-r7'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger_path=P/'ledger.json';ledger_bytes=ledger_path.read_bytes();ledger=json.loads(ledger_bytes)
assert ledger['accepted_new']==len(ledger['accepted'])==55 and not (P/'shoe-discrepancy-acceptance.json').exists()
review=json.loads((R/'review.json').read_text())['324571'];assert review['technical_pass']
integrity=json.loads((F/'evidence/independent-pass-receipts.json').read_text());assert integrity['manifest_files_verified']==1108 and integrity['frozen_verified']==2120
assert sha(R/'SHA256-MANIFEST.json')==integrity['manifest_sha256']
order=json.loads((F/'evidence/PRODUCTION-ORDER.json').read_text());hashes=json.loads((F/'evidence/PRODUCTION-HASHES.json').read_text());assert len(order)==28
assert all(sha(R/'src'/f'{n}.lean')==hashes[n] for n in order)
pdf=F/'output/pdf/shoe-discrepancy-proof.pdf';qa=dict(pdf=str(pdf.relative_to(F)),sha256=sha(pdf),pages=[dict(page=i,path=f'qa/page-{i}.png',sha256=sha(F/f'qa/page-{i}.png'),visually_viewed=True,finding='Legible; no clipping, overlaps or missing formulas; corrected page2 implementation description and page5 process chronology checked.') for i in range(1,6)],scope='Actual root image views after final generation, reporting-only; no new mathematical proof or compiler execution')
save(F/'qa/VISUAL-QA.json',qa)
readme='''Shoe discrepancy — MathDB324571 — source-only certificate

This archive contains the exact 28 independently checked production/control/print-audit source modules, plus separate audit tools/evidence. One result only: under independent equal-law strict alternating shoe draws, the source-defined discrepancy has uniform bound255/256<1 for all countable laws. Finite zero-extension, PMF normalization and arbitrary-fallback a.s. transport are included; no optimal constant is claimed.

PINS.json specifies Lean4.34.1, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and executable hashes. Upstream libraries are trusted read-only. The supplied env.sh uses this workspace's pinned installation; for another host change the package/bin locations in a NEW environment file, retaining exact versions. No upstream installation, git or network is needed on the original task host.

For a fresh rebuild, unpack in a NEW directory, create empty build/logs/receipt/tmp/cache directories, source env.sh, and run bash check.sh MODULE then bash checker.sh MODULE sequentially for every entry of PRODUCTION-ORDER.json. Use module names, not olean paths, with the pinned bin on PATH. The runner chdirs to its own directory and preserves actual exits/logs/receipts under the documented caps. Do not import original author or legacy oleans. Audit/control source tools are separate from the endpoint; their exact checked commands and exported type/body DAG/origin/closure evidence are recorded in the independent-review references.

The independent reviewer already performed both a cold28module strict/checker build and a separate empty-build source-only28module strict/checker replay. No olean is shipped here. SOURCE-HASHES.json binds every shipped production source. Only propext, Classical.choice and Quot.sound are transitive axioms. Full audit JSON is included; human-readable source/proof review is FINAL-REVIEW.md.

Access and process limitations are retained in the root acceptance record. The unread Galbraith-Holmes2012 expected-collision-time source is not claimed cleared; no specific applicable marked-color theorem was identified. No worldwide priority, full upstream rebuild, independent Lean implementation, continuous cgroup bound or optimal-constant claim.
'''
(F/'source/README.txt').write_text(readme)
archive=F/'output/shoe-discrepancy-source-only.zip';members={}
for mod in order:members[f'src/{mod}.lean']=R/'src'/f'{mod}.lean'
for name in ['PINS.json','env.sh','runner.py','write_lane.py','check.sh','checker.sh']:members[name]=R/name
members['PRODUCTION-ORDER.json']=F/'evidence/PRODUCTION-ORDER.json';members['SOURCE-HASHES.json']=F/'evidence/PRODUCTION-HASHES.json';members['README.txt']=F/'source/README.txt';members['FINAL-REVIEW.md']=R/'FINAL-REVIEW.md'
for name in ['ShoeReachableAudit']+[f'ReviewOrigins{i}' for i in range(8)]:members[f'audit-src/{name}.lean']=R/'src'/f'{name}.lean'
for q in (R/'audit').iterdir():
 if q.is_file() and q.suffix in ['.json','.py']:members['audit/'+q.name]=q
for name in ['strict-replay-evidence.json','read-resource-inventory.json','completed-receipts.json']:members['evidence/'+name]=R/'results'/name
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for name,q in sorted(members.items()):
  info=zipfile.ZipInfo(name,date_time=(2026,11,8,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16;z.writestr(info,q.read_bytes())
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None and not any(n.endswith('.olean') for n in z.namelist())
 assert all(hashlib.sha256(z.read(f'src/{n}.lean')).hexdigest()==hashes[n] for n in order)
save(F/'evidence/archive-source-check.json',dict(archive_sha256=sha(archive),production_sources=28,no_oleans=True,all_shipped_source_hashes_match=True,root_rebuilt=False,root_scope='Packaging/documentary verification only; fresh source-only compiler/checker replay already independently verified.'))
accept=dict(mathdb_id=324571,title='Uniform discrepancy bound for equal-law alternating shoe pairs',status='accepted_in_new_sixty_campaign',credit=1,accepted_utc=now,campaign_ordinal=56,
 exact_endpoint=['Shoe.sourceDiscrepancy_bound','Shoe.source_strict_universal_supremum','Shoe.countable_color_strict_universal_supremum'],
 scope='For every discrete equal shoe-color law p, under literal independent strict left/right alternating arrivals, the total variation discrepancy between the independent conditional matching-pair color and actual first chronological opposite-side match color is at most255/256. Consequently the supremum over all countable laws is strictly below1; no finite-support restriction, positive-support-only premise, simultaneous-pair/random-side replacement or unproved law identity. Actual product/conditioning/stopping/fallback/TV/countable and finite-extension bridges proved.',
 source_targets=['MathDB324571 exact raw literal, original chunk line4099 SHA6267c93aa889fa427f5e429183acdafe7fc0a283f7b3665189ae94abc033f48f','Arratia-DeSalvo arXiv1211.6486v2 Sections2,4,9.1-9.2 Conjecture4eq30','Final AAP47(2015)292-305 DOI10.1239/aap/1427814592, Conjecture4eq19'],
 paper=str(pdf.relative_to(P)),editable_paper=str((F/'source/shoe-discrepancy-proof.txt').relative_to(P)),proof_packet=str(archive.relative_to(P)),independent_review=str((R/'FINAL-REVIEW.md').relative_to(P)),keyed_gates=str((R/'review.json').relative_to(P)),root_integrity='shoe-pair-discrepancy-formal-independent-review-parent-integration-sol-r6.json',reporting_completion=str((F/'reporting-completion.json').relative_to(P)),paper_QA=str((F/'qa/VISUAL-QA.json').relative_to(P)),
 validation=dict(independent_fresh_strict=28,independent_kernel_checks=28,separate_source_only_replay_strict=28,separate_source_only_replay_checkers=28,core_modules=23,control_modules=3,named_audit_modules=2,core_origin_roots=242,control_origin_roots=17,reachable_type_body_nodes=29367,environment_metadata=428468,exact_endpoint_closures=17,nat_supremum_closure=29263,countable_supremum_closure=29308,review_manifest_verified=1108,review_frozen_verified=2120,controls='Positive chronology/singleton/normalization/unused-mass/transport/fallback controls checked; isolated noninjective coding negative fails at false equality with proper imports.'),
 axioms=['propext','Classical.choice','Quot.sound'],pins=dict(Lean='4.34.1',Lean_commit='5045d0056413266e57c625dcd7c365b10e377c52',mathlib='d13f23b723b8a846827a245b89c10fc7d3f11612'),
 substantive_reason='The all-law marked-color minorization and uniform sup bound resolve the explicit conjecture retained in the final paper. The inspected birthday/collision-time laws and source limiting-family formula do not give this law-uniform marked-color conclusion under deterministic alternation. The small/large overlap split, actual chronological block forcing and infinite-law normalization are substantive missing bridges, not formalization-only credit.',
 contrary_scope_assessment='Blocking at the birthday scale and elementary inequalities are familiar; a weak constant alone is not novelty. A routine exclusion would require a complete applicable prior-to-marked-law bridge, which neither independent review established. No optimal constant, collision-time theorem, separate countable/finite variant or global novelty certification is credited.',
 novelty_standard='Qualified bounded primary-body/current-indexed-registry/chronology/subsumption review, not worldwide priority certification.',
 current_prior_check=dict(evidence='shoe-pair-discrepancy-source-review-sol-r1/search-inventory.json; copied same-day registry inventory and exact bounded search responses, independently reconciled in r6 FINAL-REVIEW',scope='Four current root heads and bounded indexed searches; actual applicable source/Bhattacharya theorem/proof comparison, no new concrete matching marked-color theorem identified. No complete repository proof-body/history or global absence claim.'),
 prior_limits=['Galbraith-Holmes2012 expected-collision-time work404/unread across all alternate delivery; no specific applicable marked-color theorem identified; retained bounded related-source limit','No worldwide semantic/registry-tree/history/citation or live MathDB comment clearance','Pinned upstream mathematical truth/prebuilt libraries trusted, no upstream rebuild/attestation'],
 process_adjudication=dict(author_history='Historical uncapped/runpy displays, brief replay/control overlap, truncations, failed checker/render/audit attempts and late final-TV personal display remain disclosed and unwaived. Successful later replay establishes later facts, not historical universal compliance.',incomplete_review='r5 guessed two own-log paths rejected before content display; no compiler ran, frozen1596 unchanged. Retained deviation, not mathematical taint or global compliance PASS.',independent_review='r6 personally read final TV/chronology prebuild, all23core/3control bodies, performed fresh strict/checker and separate source-only replay, full graph/origin/closure validation and corrected audit strategies under unchanged caps. Its own audit -9/-6/syntax failures retained.',root_reporting='Page2 now transcribes the independently verified unrestricted-four-coordinate estimate; page5 explicitly retains late author TV display and content-vs-process distinction. All5 final pages rendered/viewed; no proof source edited or root Lean/compiler execution.',terminal_precision=integrity['terminal_display_precision_correction'],decision='Accept scientific certificate content on independently checked literal/final-source/proof/kernel/audit evidence with bounded prior and process qualifications. Do not certify historical whole-process compliance; no protected access or frozen modification is established by the failed own-log attempts. No access-control bypass or later denied retrieval permitted.'),
 trust_limits=['Leanchecker shares pinned Lean installation','Sampled process-group RSS and native image/compile-internal telemetry are not continuous/aggregate cgroup guarantees','Audit metaprograms and documentary validators are outside mathematical endpoints'],
 not_claimed=['Optimal discrepancy constant or sourceConjecture5','New birthday/collision-time theorem','Worldwide novelty/publication/journal peer review','Separate credit for helpers, numerical constant, finite or countable relabeling'],
 artifact_sha256={str(q.relative_to(P)):sha(q) for q in [pdf,archive,F/'source/shoe-discrepancy-proof.txt',F/'reporting-completion.json',F/'qa/VISUAL-QA.json',R/'FINAL-REVIEW.md',R/'review.json',R/'SHA256-MANIFEST.json',R/'TERMINAL-EXCLUSIONS.json',R/'audit/own-nodes.json',R/'audit/own-closures.json',R/'audit/origin-validation.json',R/'results/strict-replay-evidence.json']})
save(P/'shoe-discrepancy-acceptance.json',accept)
shutil.copyfile(P/'shoe-discrepancy-acceptance.json',F/'ACCEPTANCE.json')
save(F/'evidence/ledger-before.json',ledger)
assert ledger_path.read_bytes()==ledger_bytes
ledger['accepted'].append(dict(mathdb_id=324571,file='shoe-discrepancy-acceptance.json',utc=now));ledger['accepted_new']=56;ledger['status']='active_research_56_of_60_accepted';ledger['date']='2026-11-08'
ledger['latest_root_acceptance']=dict(utc=now,mathdb_id=324571,credit=1,accepted_new=56,target_new=60,previous_accepted=39,record='shoe-discrepancy-acceptance.json',qualifications='Bounded prior-access/process limits retained; no blanket historical compliance or worldwide novelty claim.')
assert len(ledger['accepted'])==56 and len({x['mathdb_id'] for x in ledger['accepted']})==56
tmp=P/'ledger.shoe-r7.tmp.json';tmp.write_text(json.dumps(ledger,indent=2)+'\n');tmp.replace(ledger_path)
manifest={str(q.relative_to(F)):sha(q) for q in F.rglob('*') if q.is_file() and q.name!='SHA256-MANIFEST.json'}
save(F/'SHA256-MANIFEST.json',dict(files=manifest,exact_self_exclusion=['SHA256-MANIFEST.json'],scope='Root archival/reporting/source-only packaging, includes copied acceptance and before-ledger snapshot. No production source or author/review lane changed.'))
assert all(sha(F/n)==v for n,v in manifest.items())
print(json.dumps(dict(accepted_new=56,total_including_prior=95,mathdb_id=324571,acceptance=str(P/'shoe-discrepancy-acceptance.json'),paper=str(pdf),archive=str(archive),root_files=len(manifest))))
