#!/usr/bin/env python3
"""Prepare unfinished research continuation, never mutate the completed packet."""
from pathlib import Path
import hashlib
import json
import re

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162j-parent'
old_path = b / 'expanded-target-2026-10-17/fresh-arithmetic-r162j-brief.txt'
old = old_path.read_text()
root = b / 'arithmetic-r162j-continuation-r1'
brief_path = b / 'expanded-target-2026-10-17/arithmetic-r162j-continuation-r1-brief.txt'
assert not root.exists() and not brief_path.exists()
iso = json.loads((o / 'prospective-isolation-continuation.json').read_bytes())
assert iso['checked_before_new_root_or_brief']
for peer in iso['peer_original_initial_briefs']:
    assert hashlib.sha256((p / peer['brief']).read_bytes()).hexdigest() == peer['brief_sha256']
prefix = '''Arithmetic162j CONTINUATION r1: finish the incomplete operative reading, then sustained research at the SAME full 4D Kakeya maximal scope.

This is NOT a new-family discovery and NOT a correctness/contribution review. The original round is sealed PREFREEZE/no nominee, with no theorem frozen and no grade/count. The broad operative-proof reading prerequisite was not attained. Complete that unfinished work and then test the preserved full target against the strongest integrated operations actually read. Do not abandon the unread central proofs for another catalogue family, rename a hard gap, restrict the target, claim a desired grade, or submit evidence administration as the research result.

Authorized Codex / GPT-6 Astra / reasoningEffort high / serviceTier default. Current campaign19/20,latestR041,one remains. All source and operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE, including former conjectures. Validate applicability/new deductions, not upstream truth. Every command workdir /home/mj-kang/Documents/Dev/math/openai-proof-research. No nested agents,git/shared writes,heavy installation,unbounded jobs or downstream formal/manuscript/release. Publication/uploads/submissions/contacts/browser UI STOPPED. Parent alone integrates and assigns gates/counts.

WRITE ONLY frontier/campaigns/2026-10-14/arithmetic-r162j-continuation-r1/ including notes/downloads/extracts/renders/temp/scratch/copies/seal. This root exists EMPTY; use it directly. The original fresh-arithmetic-discovery-r162j root is COMPLETED AND IMMUTABLE. Do not write to it,its old brief or parent. This header OVERRIDES every old assigned-root/NEW-DISTINCT/current-round instruction in the verbatim original brief below. The old namespace remains excluded from broad scans. This continuation root,brief and future parent are already covered by *arithmetic*r162* in EVERY currently recorded foreign task's ORIGINAL INITIAL brief, checked prospectively before creation. Foreign-owner recorded metadata only; no peer live body/findings/status/activity query,steering or inference is allowed.

Read the complete original brief below. Its supplied standing suffix stays verbatim (two obsolete provenance/count lines remain overridden by the current header). Retain ALL333 original wildcard guards,all no-r twins,full-relative-path casefold substring guards,plain check/activity/publication and special *t185144-*/*k369134-* aliases BEFORE the first traversal/read selection beyond exact direct exceptions. Exclude the entire arithmetic162 namespace,including the completed original,parent,briefs,copies,derivative roles and this continuation,from broad history. Own direct reads/writes are allowed only in this assigned root. No whole journal/catalogue decode. The ONLY catalogue allowance remains binary[126238,127638) Source074; no new source selection or title locator. No old broad scan rerun. Relevant specific original history may be read via exactly listed spans below; a single new prospectively pruned traversal is allowed only if an actually new construction/primitive alias requires it and is disclosed. Do not repeat the old broad query just to produce a new search receipt.

Exact completed DIRECT exceptions, relative to frontier/campaigns/2026-10-14/ (only these files; no containing namespace or linked local-body permission):
discovery-arithmetic-r162j-parent/assessment.md
fresh-arithmetic-discovery-r162j/REPORT.md
fresh-arithmetic-discovery-r162j/packet/FINAL.md
fresh-arithmetic-discovery-r162j/packet/PREFREEZE.md
fresh-arithmetic-discovery-r162j/packet/private/READING-ISOLATION.md
fresh-arithmetic-discovery-r162j/packet/private/canonical-reading.json
fresh-arithmetic-discovery-r162j/packet/private/canonical-authentication.json
fresh-arithmetic-discovery-r162j/packet/private/primary-reading.json
fresh-arithmetic-discovery-r162j/packet/private/history-reading.json
fresh-arithmetic-discovery-r162j/packet/private/include-graph.json
These exact exceptions OVERRIDE the original brief's four completed r162i exceptions; do not open those older bodies anew. Metadata is planning, not semantic reading. Do not follow original local-copy fields into protected bodies. Retrieve fresh canonical/primary copies into YOUR root. Original-history direct exceptions additionally allow exactly frontier/iterations/i02-crossfield.md[19832,23165) and frontier/iterations/i124-fractal-incidence-discovery.md[13346,22638), complete original sections through their equal-level endings. Record actual own reading,not a predecessor's claim.

Original result and unresolved obligations (retain all quantifiers and supplied old dispositions):
The unchanged UNFROZEN full target is, for EVERY epsilon>0,a finite C_epsilon,EVERY 0<delta<1 and EVERY f in L4(R4), ||K_delta^(4) f||_L4(S3)<=C_epsilon delta^(-epsilon)||f||_4. K takes the supremum over ALL centers of normalized averages on straight unit Euclidean tubes of radius delta. No favorable direction subset,regular center map,compactness,dense shading,semialgebraic support,two-ends condition or prescribed normal is an added hypothesis. Its finite shaded-family reduction retains arbitrary measurable Y(T),EVERY positive lambda and delta-separated directions,with lower bound c_epsilon delta^epsilon lambda^4 N delta^3. It is NOT the protected older sparse temporal-sampling target or paid plane-direction bound,though sparse-law normalization interfaces overlap and must be credited.

Read the whole prior PREFREEZE derivation before adding new calculations. It pays: monic-cubic root exclusion for arbitrary measurable time fibres, giving fourth-power Jacobian integral; a capped-Jacobian pushforward; K3 projected L^(3/2) control with the exact directional marginal; fixed-normal-band density range; actual primary four-dimensional incidence baseline and fixed-point exponents. Two focusing selectors disprove overstrong raw/capped pointwise multiplicity shortcuts,not the full maximal target. These are paid deductions/repairs,not nominees.

Unpaid: substantial-mass overlap control for the capped transport OR a compatible hidden-density estimate on the SAME retained projected good mass. The attempted K4 import obtains positive density growth but original-prior domination,assignment cleaning,list/recovery and normal-label overlaps still cost polynomial factors at lambda=delta^a. Dividing the successful incidence law by lambda loses domination by the original independent-time prior. No actual nonroutine operation closes that full interface yet. Naming it is not a result; carry the strongest compatible source/primary operations through the real budgets before declaring a gap.

Finish the reading prerequisite BEFORE further extended deductions or drafting. Authenticate both exact Source074 canonical folders and all35 blobs against complete-tree metadata; include graph and actual wrappers govern,never guesses. In THIS continuation semantically read the complete mathematical TeX/text of BOTH canonical manuscripts and all actual mathematical includes/appendices/consequences/figures. Do not count predecessor265,136bytes as your own reading. The total canonical non-PDF text is1,019,669bytes. Prior reading left central K3 local/stationary/angular/entropy/projection and first closure proofs unread,and most K4 comparison/critical-path/scalar/isotropic/retained-edge/finite-rate/unbounded-rate proofs unread. Those are central possible resources for this exact mass-budget gap. Read them completely in manageable contiguous chunks,record exact extents/recovery,keep durable understanding notes,and do not replace them with interface statements or hashes. Compiled PDFs may be authentication-only if all mathematics is read in actual source; disclose honestly. Diagram TeX reading vs rendered visual inspection must be distinguished.

Then read the strongest relevant ACTUAL primary proof operations before further extended mathematics: complete Katz-Rogers polynomial-Wolff argument; actual Borges et al. incidence/maximal proof and any recursive planebrush,trilinear,two-ends operations used to strengthen or compose its density powers; the operative Guth-Wang-Zahl geometric/density/clustering proofs on which the proposed transfer relies. The previous GWZ read was interface-only and the recursive Borges companions unread. A cited theorem statement or another agent's claim does not discharge a new applicability argument. Authenticate/version URLs and record precise own primary/transitive extents,partial/unread proofs and access failures. Complete strongest relevant proof reading proportionately; do not turn this into an unbounded audit of all literature or of stipulated upstream truth.

After those reads, continue sustained concrete full-scope mathematics. Try a genuine loss-balanced source/primary composition paying mass and normal-label costs inside the FOURTH density power,or another CLOSED compatible full-target operation; preserve both successes and failed routes in durable notes. Do not force the capped-transport criterion if a stronger compatible method bypasses it. Verify the exact joint distributions,independent-time contract,retained fractions,delta/lambda exponents,chart/list multiplicities,geometric support and quantifier budgets. Numerical checks are diagnostics,not proofs. A source/classical composition can be compatible even when a naive shortcut fails; credit the strongest completed payment before a substantial-contribution claim.

No old scope is changed. Arithmetic162i's entire original distance law remains unproved. Arithmetic162h and the other supplied whole PASS/TECHNICAL theorems remain condition-DISCHARGED,ZERO count,no retry/downstream work. Prior Analytic154 plane-direction composition paid; Analytic158 fixed-power sparse sampling target unpaid. Do not substitute a special case for the unchanged present full target or any older target. If a distinct viable full theorem emerges,freeze exact statement BEFORE author-proof development and construct the full proof under explicit source dependencies,with strongest-payment comparison. No self-grades/count. If nothing closes,report honest PREFREEZE/no nominee with concrete integrated derivation and exact remaining gap. If required readings again remain unfinished,state that openly and preserve the unfinished work;do not claim strongest-proof clearance or research completion.

Seal only YOUR new exact packet once,with fresh manifest,detached FINAL/MANIFEST/outside REPORT anchors and a read-only explicit-anchor verifier. Proportionate tiny COPIED own-text controls only. Protected canonical/primary/history/search/render/copied bodies AND named metadata stay private/local under original rights; do not copy an inherited manifest into a reduced selection. Artifact verification is not a mathematical gate. Final handoff must distinguish newly completed reading and mathematics from preserved predecessor calculations,retain full target and exact unpaid interfaces,and disclose all actual limits. Parent alone integrates and requests independent correctness plus separate contribution review of any viable full author proof.

--- VERBATIM ORIGINAL ARITHMETIC162J ASSIGNMENT (current continuation header overrides old root/current-round/exceptions) ---
'''
brief = prefix + old
old_guards = set(re.findall(r'\*[^\s,;()]*\*', old))
assert old_guards <= set(re.findall(r'\*[^\s,;()]*\*', brief))
marker = '--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
assert len(brief.split(marker, 1)[1].encode()) == 5570
root.mkdir()
brief_path.write_text(brief)
prep = {'path': brief_path.relative_to(p).as_posix(), 'root': root.relative_to(p).as_posix(),
        'bytes': len(brief.encode()), 'sha256': hashlib.sha256(brief.encode()).hexdigest(),
        'old_literal_guards_preserved': len(old_guards), 'standing_suffix_bytes_unchanged': 5570,
        'original_full_assignment_verbatim': True, 'same_full_target_unchanged': True,
        'new_family_claim': False, 'review_or_grade_retry': False,
        'foreign_initial_guards_before_creation': len(iso['peer_original_initial_briefs'])}
(o / 'brief-preparation.json').write_text(json.dumps(prep, indent=2) + '\n')
args = {'clientRequestId': 'twenty-20261023-arithmetic-r162j-continuation-codex-astra-r1',
        'target': {'providerInstanceId': 'codex', 'model': 'gpt-6-astra',
                   'options': {'reasoningEffort': 'high', 'serviceTier': 'default'}},
        'mode': 'async', 'role': 'research',
        'title': 'Arithmetic162j continuation: complete operative reading and full-scope research',
        'task': brief}
(o / 'private/submitted-prompt.json').write_text(json.dumps(args, indent=2) + '\n')
print(json.dumps(prep, indent=2))
