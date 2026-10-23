#!/usr/bin/env python3
"""Prepare mutually isolated reviews of one entire immutable author theorem."""
from pathlib import Path
import hashlib
import json
import re

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'arithmetic-r162m-nominee-parent'
author = b / 'fresh-arithmetic-discovery-r162m'
original = (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162m-brief.txt').read_text()
frozen = (author / 'packet/FROZEN-THEOREM.md').read_text()
proof = (author / 'packet/AUTHOR-PROOF.md').read_text()
sha = lambda d: hashlib.sha256(d).hexdigest()
assert sha(frozen.encode()) == '9b967d5563e22bd8b07283d34d574f5eed9d5e2dc696020835e4e12655d003e1'
assert sha(proof.encode()) == '6dd830369698429d2d3d713a07a11a895e68e52ee650e231ff7833219e58b3e3'
iso = json.loads((o / 'prospective-review-isolation.json').read_bytes())
assert iso['checked_before_both_review_roots_and_briefs']
for peer in iso['peer_original_initial_briefs']:
    assert sha((p / peer['brief']).read_bytes()) == peer['brief_sha256']
old_guards = set(re.findall(r'\*[^\s,;()]*\*', original))
common = '''Authorized Codex / GPT-6 Astra / reasoningEffort high / serviceTier default. Campaign19/20,latestR041,one remains. This is REVIEW ROUND1 of the ENTIRE unchanged frozen author theorem,not discovery,not a proof repair,not a favorable-grade retry. No prior independent review finding,response or unresolved reviewer objection exists in this round. The author reports no gap;that is NOT a gate. Parent adopts gates/counts only after independent assessment.

ALL source theorems and operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE,including formerly open claims. Review new deduction/applicability and full scope,not upstream truth. The original research assignment below is included VERBATIM;this review header overrides its old assigned-root,discovery/freezing and four completed-exception instructions. It does not override pin truth,acceptance criteria,old immutable scopes or path exclusions. Obsolete18/20 and Factory-only lines remain overridden. EVERY shell command workdir /home/mj-kang/Documents/Dev/math/openai-proof-research. No nested agents,git/staging/commit,shared edits,heavy installations,unbounded jobs,public actions,contacts,uploads/submissions,browser UI or downstream formal/manuscript/release. All reviewer-created notes,downloads,temp,copies,extracts,renders,scratch,controls and seal stay inside YOUR exclusive root. Root exists EMPTY,use it directly. Parent alone integrates.

Freeze and proof bindings,relative to frontier/campaigns/2026-10-14/:
fresh-arithmetic-discovery-r162m/packet/FROZEN-THEOREM.md
bytes1645;SHA2569b967d5563e22bd8b07283d34d574f5eed9d5e2dc696020835e4e12655d003e1.
fresh-arithmetic-discovery-r162m/packet/AUTHOR-PROOF.md
bytes17147;SHA2566dd830369698429d2d3d713a07a11a895e68e52ee650e231ff7833219e58b3e3.
Both whole texts follow in this prompt. Read the ACTUAL bound files too;do not substitute prompt bytes for artifact authentication. Author files are immutable;record pre/post hashes and modes. No edits/normalization/repair even if a flaw is found. A necessary repair must address the same entire theorem in a later parent-owned round,not quietly replace it by a restricted statement.

Author packet detached anchors:
packet/FINAL.md 392e4da2db6bf09d8909bfc617076f74d0276857a86aa276ce1a24bdd669fe5e
MANIFEST.json e60d17ab380041e6276a3b1c9849e5e5d5c4b33c9f8fcedba9e31df280b511c5
REPORT.md 6ecd286c9a85c25529297378d7f8f4cffc9531e0da1cbbd78159bcf9a5ed85ba
96-file author packet verified by parent;this is bytes only,not a mathematical gate. Read the actual verifier before any read-only run. Do not copy an inherited manifest onto your own reduced review selection.

EXACT COMPLETED direct author inputs (relative to fresh-arithmetic-discovery-r162m/;no containing namespace or linked local-body permission):
REPORT.md
ANCHORS.json
MANIFEST.json
packet/FROZEN-THEOREM.md
packet/AUTHOR-PROOF.md
packet/FINAL.md
packet/verify_packet.py
packet/private/FREEZE-RECEIPT.json
packet/private/PREFREEZE-CALCULATIONS.md
packet/private/AUTHOR-CHECK.md
packet/private/SOURCE-INTERFACE.md
packet/private/SOURCE-UNDERSTANDING.md
packet/private/READING-ISOLATION.md
packet/private/canonical-selection.json
packet/private/canonical-authentication.json
packet/private/canonical-reading.json
packet/private/primary-reading.json
packet/private/PRIMARY-UNDERSTANDING.md
packet/private/primary/acquisitions.json
packet/private/original-reading.json
packet/private/original-selection.json
The original brief's four older completed exceptions are SUPERSEDED;do not open them. Read these exact actual author inputs fully at relevant mathematical scope. Protected metadata is navigation,not proof reading. Do not follow author local-copy fields into protected body namespaces. Retrieve fresh pinned canonical/primary copies into YOUR root. The explicitly enumerated ORIGINAL-history paths/spans in original-reading.json are additionally authorized direct exact reads of ONLY those spans through their stated endings;their whole-file hashes are metadata,not whole-body reading permission. No linked archive or namespace expansion.

Before any filename traversal or body selection beyond exact direct instructions/exceptions,retain every original literal wildcard/no-r twin and full-relative-POSIX path.casefold substring guard below. Also explicitly install BOTH roles' patterns:
*arithmetic*r162m-proof* *arithmetic*162m-proof* *arithmetic*r162m-contribution* *arithmetic*162m-contribution*
The ENTIRE author/parent/brief/review/derivative arithmetic162 namespace remains excluded from broad history;the exact direct author list is the sole exception. Both roles are mutually excluded from their INITIAL briefs. Do not inspect,query,infer or use the other review's root,body,findings,status,activity,prompt or result. No live peer/foreign task query or steering. Foreign original initial *arithmetic*r162* guards covered both review roots/briefs before creation;this is prompt chronology,not OS/perfect isolation or fresh liveness. No broader old scan rerun. One prospectively pruned ORIGINAL-history traversal for actually relevant construction/primitive aliases is allowed if needed;include eligible hidden/ignored/large/JSON/TeX/Bib UTF8 without filesize cutoff after pruning. No projectwide rg then filter or broad untracked inventory. Disclose false admissions/coarse omissions and exact read extents;no exhaustive clearance/priority claim.

Actual proof reading precedes extended review drafting. Metadata,hashes,abstracts,another agent's summaries or an author's reading ledger are not your own semantic reading. Authenticate all29 canonical Source077 blobs against the complete13223-entry nontruncated tree (SHAeeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b),using fresh pinned raw paths. Both actual build/paper.tex wrappers and their mathematical operative includes/companions must be read at the proof-operation scope needed for full assessment. Read actual graph theorem L3->Lq ALLq>3,its full rough chart/Jacobian transfer including smooth boundary,and every stronger integrated source operation relevant to the proposed bridge. All these operations are stipulated paid;do not audit their truth. Ignore truncated tree.json. Catalogue allowance remains ONLY binary Source077[130739,132535);no locator or new family selection. No need to open it if canonical paths suffice.

Read strongest compatible ACTUAL primary proofs and relevant ORIGINAL-history mechanisms before extended assessment. The author comparison includes concentration/profile extraction,off-scaling compactness,local/global extremizer arguments and the elementary analytic/convexity mechanisms;check their exact hypotheses and composition,not just abstracts. Author canonical text reading is complete,while external transitive primary gaps remain explicitly disclosed. Resolve essential proof/application gaps needed for YOUR verdict,or report them as incomplete;never count unattempted/inaccessible/unread originals as read. Record URLs/versions,own exact extents,late reads,truncation recoveries,access failures and semantic limits. No claim of all-literature or all-transitive clearance.

Entire frozen scope includes EVERY normalized rough COMPLEX Lp extremizing sequence,EVERY finite3<p<infinity,and EVERY nonempty compact smooth embedded definite-curvature two-surface inR3,including smooth boundary/disconnected chart descriptions. Fixed-surface constants only. Strong subsequence compactness modulo the stated plus-sign modulations,norm attainment and qualitative stability relative to the ENTIRE extremizer set all require assessment. No smooth/bounded/nonnegative input,even-integer p,restricted chart/subsequence of surfaces,off-diagonal q>p replacement,endpoint,classifying constant functions or uniform-family rate may replace it.

The claimed proof uses a stronger paid L3->Lq interface,an output exponent q0 belowp,an L2 extraction exponent q1 abovep,and fixed-J Brezis-Lieb identities. It does not assume uniform Lp residual bounds inJ or Hilbert-normalized extremality. Weighted square mass,complex dislocation/analytic injectivity and plus/minus strictness are central claims,not adopted findings. Reconstruct the complete argument and all compatibility/normalization steps independently. The author-check file is an assertion to test,not independent evidence. No preselected outcome or gate is requested.

Keep public original review prose/code separate from private source/primary/history/search/copied/render bodies AND their named metadata under original rights. Seal YOUR own exact review packet once with a fresh manifest,detached FINAL/MANIFEST/outside REPORT anchors and read-only explicit-anchor verifier. Proportionate tiny COPIED own-text controls only;avoid administrative test-suite growth. Artifact checks never assign mathematical gates. Original author bytes/modes remain unchanged. Final handoff gives whole-scope verdict,full operative derivation or precise remaining objections,actual reading/limits,immutable input checks and detached anchors. No acceptance,count,public action or downstream work. Parent alone adopts the independent result.

'''
roles = {
    'proof': '''YOUR SOLE GATE: independent adversarial FULL CORRECTNESS for the ENTIRE unchanged frozen theorem and proof. Do NOT assign substantiality,acceptance or count. Return PASS only if every frozen assertion and every essential mathematical dependency/application is established,relative to stipulated upstream truth. Return NEEDS_REPAIR with precise necessary author correction(s),counterexamples or invalid deductions if found;check whether the full statement survives rather than calling a flawed lemma a full disproof. Return INCOMPLETE if an essential correctness verification remains unpaid,with exact missing operation/access/read extent. No restricted PASS,no checklist-only verdict,no reliance on the other gate. Independently reconstruct source(A),all interpolation/exponent cases including3<p<4,nonvanishing/decay/dislocations,countable nested extraction and one diagonal subsequence,all finite-J output bounds and uniform-in-J OUTPUT remainder,weak Lp membership of original-sequence profiles,weighted square-mass tests and equality chains,complex strictness/analytic overlap,modulation signs,strong convergence,and entire qualitative stability. Do not invent an unneeded endpoint or uniform-surface hypothesis. Supply complete derivations and dispose of each genuine objection at full scope.\n\n''',
    'contribution': '''YOUR SOLE GATE: independent FULL SUBSTANTIAL-CONTRIBUTION assessment,CONDITIONAL ON CORRECTNESS of the ENTIRE unchanged frozen theorem. Do NOT assign correctness PASS,acceptance or count;do not inspect the other gate. Return SUBSTANTIAL only for a closed identifiable nonroutine operation beyond the strongest compatible integrated source/actual primary/history payment,with precise proof-level comparison at EVERY frozen conclusion. Return TECHNICAL only if you supply an integrated compatible source/classical derivation covering the ENTIRE unchanged scope,including complex Lp normalization,all strict p>3,rough inputs,smooth boundary,every extremizing sequence,compactness/attainment AND qualitative stability. A familiar individual lemma,headline,named method or partial theorem is insufficient for a full technical verdict. Test strongest abstract/profile/variational operations and their actual hypotheses together,including whether the two-output-exponent argument and local square-mass/analytic exclusion already follow by compatible classical operations. A naive off-diagonal proof failing atq=p is not proof of a nonroutine residual if another known composition pays it. Conversely do not erase a real compatibility gap by invoking general concentration compactness without a full derivation. Return INCOMPLETE if an essential full-scope comparison/read/dependency remains unresolved,with exact paid/unpaid split. If a suspected mathematical issue arises,explain its consequence conditionally and preserve the separate correctness gate. No grade shopping,restricted replacement,literature-priority or worldwide-impossibility claim.\n\n'''
}
prepared = []
for role, instructions in roles.items():
    root = b / ('arithmetic-r162m-' + role + '-r1')
    path = b / ('expanded-target-2026-10-17/arithmetic-r162m-' + role + '-r1-brief.txt')
    assert not root.exists() and not path.exists()
    prefix = 'Arithmetic162m independent ' + role + ' review ROUND1.\nWRITE ONLY ' + root.relative_to(p).as_posix() + '/.\n\n'
    brief = prefix + instructions + common
    brief += '\n--- ENTIRE IMMUTABLE FROZEN THEOREM ---\n' + frozen
    brief += '\n--- ENTIRE IMMUTABLE AUTHOR PROOF (unreviewed) ---\n' + proof
    brief += '\n--- VERBATIM ORIGINAL RESEARCH ASSIGNMENT (review header overrides old root/role/exceptions) ---\n' + original
    assert old_guards <= set(re.findall(r'\*[^\s,;()]*\*', brief))
    marker = '--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
    assert brief.split(marker, 1)[1] == original.split(marker, 1)[1]
    root.mkdir()
    path.write_text(brief)
    args = {'clientRequestId': 'twenty-20261023-arithmetic-r162m-' + role + '-codex-astra-r1',
        'target': {'providerInstanceId': 'codex', 'model': 'gpt-6-astra',
            'options': {'reasoningEffort': 'high', 'serviceTier': 'default'}},
        'mode': 'async', 'role': 'review',
        'title': 'Arithmetic162m: independent full ' + ('correctness review' if role == 'proof' else 'substantial-contribution review'),
        'task': brief}
    (o / 'private' / (role + '-submitted.json')).write_text(json.dumps(args, indent=2) + '\n')
    prepared.append({'review_role': role, 'root': root.relative_to(p).as_posix(),
        'brief': path.relative_to(p).as_posix(), 'brief_bytes': len(brief.encode()),
        'brief_sha256': sha(brief.encode()), 'old_literal_guards_retained': len(old_guards),
        'standing_suffix5570bytes_unchanged': True, 'original_assignment_verbatim': True,
        'whole_frozen_and_proof_verbatim': True, 'initial_mutual_exclusions': True,
        'frozen_sha256': sha(frozen.encode()), 'proof_sha256': sha(proof.encode()),
        'clientRequestId': args['clientRequestId']})
(o / 'review-preparation.json').write_text(json.dumps(prepared, indent=2) + '\n')
print(json.dumps(prepared, indent=2))
