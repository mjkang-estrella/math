"""Seal once after review and copied controls. Writes only the three outside envelopes."""
from pathlib import Path
import importlib.util,json,hashlib,datetime
R=Path(__file__).resolve().parent
for n in ['REPORT.md','FINAL.json','MANIFEST.json']:
 if (R/n).exists():raise SystemExit('Refusing reseal: envelope exists')
spec=importlib.util.spec_from_file_location('own_v',R/'verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
# Narrow unchanged selected-original observation immediately before sealing.
mem=json.loads((R/'incoming-membership.json').read_text())
for x in mem['members']:
 if v.digest(Path(x['origin']).read_bytes())!=x['sha256']:raise SystemExit('Selected original changed: '+x['origin'])
files,dirs=v.inventory(R)
m={'schema':1,'files':files,'directories':dirs,'limits':'Exact own packet bytes only; no mathematical, historical whole-parent, first-read or OS certification.'}
(R/'MANIFEST.json').write_text(json.dumps(m,sort_keys=True,indent=2)+'\n')
mh=v.digest((R/'MANIFEST.json').read_bytes())
report='''# H138 first independent correctness handoff

**PASS** for the whole unchanged frozen H, relative to the stipulated pin and operative source proofs. No new local-uniformity axiom, frozen-byte repair or scope reduction was used. REVIEW.md gives detailed analytic checks C1–C9, including arbitrary past/future controls, finite neighboring windows, scheduling compatibility, quotient sign, common product continuity and every-radius growth. No remaining mathematical objection was found within that dependency boundary.

For EVERY 4/9<v<1 and 1<c<9v/4, the result is ONE complete smooth metric on R^3, Euclidean near zero, Ric>=0 everywhere, normalized AVR=v, and strictly increasing positive integers k_i tending to infinity with dim_R H_(k_i)>=c(k_i+1)^2 for EVERY i. Functions are real smooth entire harmonic functions with an individual finite C_u satisfying |u(x)|<=C_u(1+d_g(0,x))^(k_i) at EVERY point on that SAME metric. No unique tangent cone, uniform growth constants, prescribed degree sequence, all-large-degree, endpoint or extra curvature assertion is added.

Correctness is separate from contribution: **UNREVIEWED contribution**, **zero acceptance/count**. Parent alone integrates/reviews/counts. No peer finding was a premise. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and operative proofs remain stipulated true, not truth-audited. Scope/proof/prefreeze derivation retain their incoming hashes.

Actual proof reads and protected source/primary/current-original bindings are in the three reading ledgers. READING-LIMITS.md discloses initial unpruned filename navigation, broad derivative false admissions in the first retained scan, a residual old replay derivative in the second, truncation recovery, unused transitive proofs, a corrected GK archive-wrapper check, and late selected-original observation limits. No whole-history, whole-author-root, historical whole-parent, OS-isolation, latest-version, priority, formal or contribution certification is claimed. Reduced incoming-copy membership and actual selected-original authentication are explicitly separated. The incoming verifier was read but not executed because its traversal lacks the current exclusions. All 54 selected source/original observations matched intake snapshots before sealing.

Six copied artifact controls passed, including four expected rejection cases; three copied-control source originals were unchanged. These tests and exact hashes are NOT mathematical gates. Original review prose/code and metadata are separate from protected bodies under private/. All writes stayed in this exclusive root; no git, children, installation, browser UI, contacts, uploads or downstream work occurred. Provenance: Codex / GPT-6.1-Sol / high / default service tier.

This packet is sealed once. MANIFEST binds its exact payload and directories; REPORT/FINAL/MANIFEST are separate envelopes. Use the externally returned three SHA256 anchors with the read-only verify.py. Do not repair or reseal original packets.
'''
(R/'REPORT.md').write_text(report);rh=v.digest((R/'REPORT.md').read_bytes())
f={'schema':1,'candidate':'H138','round':'FIRST independent adversarial correctness review','correctness':'PASS','coverage':['C1','C2','C3','C4','C5','C6','C7','C8','C9'],'scope_unchanged':True,'scope_sha256':'82e7f37c36205cc62e52fc6ad037072706405efb7302dafa395747a2c5b2ff53','author_proof_sha256':'fc1228c5dc20b373fcba3b176ccb6b26e30bc099647e4dc8d5762a3833355258','prefreeze_derivation_sha256':'948045c339782a0d46f1cd86eba05df10fef5c6f106e98b64393412fbe868a31','freeze_utc':'2026-10-21T00:36:26.664416+00:00','stipulated_pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','operative_source_proofs_stipulated_true':True,'new_local_uniformity_axioms':False,'mathematical_repairs':[],'remaining_mathematical_objections':[],'contribution':'UNREVIEWED','acceptance_assigned':False,'count_change':0,'parent_alone_integrates_reviews_counts':True,'official_count_observed':'19/20; latest R041; one remains; not changed here','reading_limits':'READING-LIMITS.md','review':'REVIEW.md','rights':'Original review prose CC BY 4.0; original code MIT; copied protected material retains original rights and remains private/local','provenance':'Codex / GPT-6.1-Sol / high / default service tier','manifest_sha256':mh,'report_sha256':rh,'sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(R/'FINAL.json').write_text(json.dumps(f,sort_keys=True,indent=2)+'\n')
a={'MANIFEST.json':mh,'REPORT.md':rh,'FINAL.json':v.digest((R/'FINAL.json').read_bytes())}
print(json.dumps({'detached_anchors':a,'read_only_verification':v.verify(R,a)},indent=2))
