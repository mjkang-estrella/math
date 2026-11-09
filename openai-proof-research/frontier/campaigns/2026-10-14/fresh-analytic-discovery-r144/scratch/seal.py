from pathlib import Path
import json,hashlib,os
r=Path(__file__).resolve().parents[1]
outside={'FINAL.md','MANIFEST.json','REPORT.md'}
assert not any((r/n).exists() for n in outside), 'refusing second seal'
final="""# Analytic discovery r144 — PREFREEZE / no nominee

One family: Source375, quartic Allen–Cahn finite Morse index, with the old full dimensions4–7 scope unchanged. No frozen theorem, complete author-proof nominee, independent grades, acceptance/count or downstream stage.

DERIVATION.md and LOCALIZATION-DETAILS.md develop moving cylindrical exclusion, capped reach, fourth-power cutoff algebra and shell summation. These remove the earlier fixed-core scalar error obstruction, conditional on a localized fourth-moment estimate. They do not prove that coupled PDE estimate.

The exact unpaid operation is a simultaneous exterior version of the source growth/bad-net and radial physical gluing constructions, with quantitative cap, collar, normal-lift and contact-transfer errors, before outer exhaustion. Compatible local stable-ball regularity is already supplied by the read primary theorem. No reduced target or supporting substitute is nominated.

Read GAPS.md for the preserved full target and final scope; READING-LIMITS.md and ISOLATION.md for actual proof extents, false admissions, truncations and exclusions; SOURCE-AUTH.json, PRIMARY-AUTH.json and AUTH-RECHECK.json for separate authentication; VERIFY-README.md for read-only replay.

Authorized Codex/GPT-6 Astra/high/default tier requested; actual tier not independently observed. Campaign19/20/latestR041. Pin and operative proofs stipulated true. All writes are inside this exclusive root; no git, agents, publication or downstream work. Parent alone integrates, reviews and counts.

This is an artifact seal, not a theorem freeze or mathematical gate. Three detached envelope SHA256 anchors are supplied in the terminal handoff.
"""
report="""# Outside report — r144

PREFREEZE/no nominee. The full existing target is unchanged: for every4≤n≤7, every finite-Morse-index C² solution of Δu=u³−u on R^n with values in[-1,1] is a constant well or a planar tanh transition. No author proof of that claim is submitted.

The actual r23 originals already identified automatic energy growth as missing. This round worked within that same distinct-from-r143 family and did not rename the gap. After reading the pinned growth/radial operations, the author obtained a more favorable moving-core calculation: cylinder energy is bounded by CK(w)s^(7−n)w^(n−1), and a fourth-order collar loss would have summable normalized cost O(K(R)^(-(n−3)/2)). The choice w=L+s^(1/50), L=R/√K(R), also fits polynomial buffers. Fourth-power Young/transfer estimates handle zero cutoff values algebraically. These are supporting feasibility calculations, not the necessary exterior PDE estimate.

The full coupled localization is unfinished: physical square-root test admissibility and normal averaging, localized exponential-kernel leakage, cap-branch payments, positive-foot transfer and final radial switching/area comparison have not been proved together with one uniform set of constants and limits. A compatible primary local stable-ball theorem is already available and was read. The earlier dimension-four fixed-cylinder estimate is therefore not presented as an impossibility barrier.

Strongest known compatible classification retains a bounded-energy assumption: Florit-Simon arXiv:2602.03136v1 Theorem1.2 with the stipulated stable input, and Liu et al arXiv:2610.08499v1 finite-index theorem/corollary. Their relevant actual proof bodies were read to the extents recorded; they obtain finite blowdown mass from the assumed energy bound. The full transitive WW proof and all source reach/mean-curvature operations were not freshly read. No literature-wide novelty claim.

Fourteen canonical pinned blobs match complete-tree path,size,Gitblob andSHA256. Three incoming primary archives and five selected members match their separate records. One optional primary request returned404. Thirteen selected local-original records rechecked unchanged from their earlier local-auth record. The initial broad scan falsely admitted derivative aliases; the corrected scan remains coarse. All limits and clipped outputs are disclosed. There is no perfect-isolation or exhaustive-history certificate.

Six separately manifested copied-prose integrity controls behaved as expected. The final exact manifest covers all actual payloads, including private inputs and nested fixture envelopes; it excludes exactly the three root outside envelopes. Detached envelope anchors are computed independently in the terminal and required by the read-only verifier. No inherited original manifest certifies a reduced copy. Protected bodies remain private/local under their original rights.

No independent correctness/contribution grades, acceptance/count, formalization, manuscript or release. No shared-root edits, git or publication. Parent alone decides further work. All old full/technical/failed scopes and stipulated dispositions remain unchanged.
"""
(r/'FINAL.md').write_text(final)
(r/'REPORT.md').write_text(report)
records=[]
for base,ds,fs in os.walk(r,followlinks=False):
    for n in ds: assert not (Path(base)/n).is_symlink()
    for n in fs:
        p=Path(base)/n
        assert p.is_file() and not p.is_symlink()
        name=p.relative_to(r).as_posix()
        if name in outside: continue
        b=p.read_bytes()
        records.append({'path':name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
records.sort(key=lambda e:e['path'])
m={'schema':'r144-exact-payload-v1','scope':'entire own root except exactly three root envelopes',
   'outside_envelopes':sorted(outside),'files':records}
(r/'MANIFEST.json').write_text(json.dumps(m,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'payload_files':len(records),'payload_bytes':sum(e['size'] for e in records),'outside_envelopes':3}))
