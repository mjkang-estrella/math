#!/usr/bin/env python3
"""Compose the two Arithmetic156 round-1 review briefs from the current guard header and the A147 review template."""
import hashlib, json, pathlib, sys

C = pathlib.Path(__file__).resolve().parents[1]
ET = C / "expanded-target-2026-10-17"
s189 = (ET / "fresh-structural-r189-brief.txt").read_text().split("\n")
a147 = (ET / "arithmetic-r147-proof-r1-brief.txt").read_text().split("\n")

# Header/guards from the current discovery brief (lines 2..38 zero-based: blank through last guard supplement).
header = s189[2:38]
assert header[-1].startswith("Additionally install prospective FULL-PATH wildcard guards *arithmetic*r160*")
assert s189[9].startswith("Also individually install *arithmetic*r136*")
peer_old_start = s189[9].index("The ORIGINAL INITIAL briefs of Arithmetic156 and Arithmetic157")
peer_old_end = s189[9].index("Exact COMPLETED exceptions do not widen containing directories.") + len("Exact COMPLETED exceptions do not widen containing directories.")
peer_new = ("The ORIGINAL INITIAL briefs of Arithmetic157 and Structural189, the two live peers, already contain the literal prospective guard *arithmetic*r156* before either review root/brief existed, so both review roots are covered. "
            "Exclude the ENTIRE *arithmetic*r157* and *structural*r189* namespaces and every body/parent/brief/copy/derivative/status/activity alias. "
            "Exclude every other arithmetic156 review role and all broad arithmetic156 author/parent/brief/copy/status/activity selection; only the exact completed AUTHOR inputs and the parent assessment/questions specified below are directly admitted. "
            "BOTH new review briefs prospectively exclude the other role before either is dispatched. "
            "Arithmetic155, Structural188, Structural187, Arithmetic154, Arithmetic153, Structural186, Arithmetic152, Arithmetic151 and Arithmetic150 are COMPLETED PREFREEZE/no nominee and parent-archived; exclude their namespaces from all selection; no completed-round exception is admitted in this review. "
            "Do not inspect or steer any peer to certify isolation, read the other review's findings or infer its verdict. This is prompt chronology, not OS/perfect isolation. Exact exceptions do not widen containing-directory admission.")
header[7] = s189[9][:peer_old_start] + peer_new + s189[9][peer_old_end:]
assert header[7].index("Own root excluded") < header[7].index(peer_new)
for bad in ("Arithmetic156 and Arithmetic157 already", "Structural188, Arithmetic155, Structural187", "Own structural189 namespace"):
    assert bad not in header[7], bad

role_proof = ("Role: independent adversarial FULL CORRECTNESS review ONLY. Reconstruct every new deduction at the ENTIRE unchanged frozen scope. Check source-construction applicability and the enlarged generic choice, simultaneous curve genericity and jet separation, smoothness and free inertia of each one-factor surface, the I2 two-node model and the PRIMITIVE integral vanishing-cycle relation, the explicit finite Galois cover and its genus, positivity and stack-Lefschetz hypotheses in dimensions four and three, the universal-cover disc van Kampen and direct limit, the four-factor product transports and section liftings, identification with the dominating source component, exactness of pi1(F)->pi1(Y)->pi1(R)->1 with every upstairs divisor and the exact root-meridian kernel, and items (2)-(4) through prop:transfer. Return PASS only if the unchanged theorem AND unchanged proof establish every assertion and no essential verification remains incomplete. Otherwise NEEDS_REPAIR for actual necessary corrections or INCOMPLETE for essential uncompleted verification, with exact evidence/quantifiers. Do not silently replace a missing argument and mark the original PASS. No contribution verdict, acceptance or count.")
role_contrib = ("Role: independent FULL-SCOPE SUBSTANTIAL-CONTRIBUTION review ONLY, CONDITIONAL on correctness of the ENTIRE unchanged theorem. Do not issue a correctness grade or read/infer the correctness role. Pay the strongest compatible actual source/primary/classical/history derivation, including the source eightfold construction with its surjection and submersion witnesses, pi1(S)=pi1^orb(base) for elliptic surfaces with at least one singular fibre and multiple fibres, Nori/Campana-type orbifold exact sequences for fibrations with multiple fibres, Lefschetz-thimble handle decompositions over discs and stack Lefschetz for Deligne-Mumford stacks. TECHNICAL requires an integrated derivation covering EVERY frozen assertion and quantifier, not merely naming folklore or leaving compatibility unpaid. For SUBSTANTIAL identify and substantiate the exact CLOSED residual beyond those operations at the same full scope (the author proposes one-factor stack Lefschetz plus the primitive two-node relation, transport through the other smooth factors and the exact root-meridian kernel identification). If an essential comparison cannot be completed, return INCOMPLETE with that exact remaining assessment step. A strong headline, unread original or access failure is not evidence of novelty. No correctness verdict, acceptance/count, scope weakening or desired-grade shopping.")

common = [
    "THIS IS AN INDEPENDENT REVIEW, overriding original standing discovery/freeze/author-development instructions. Review the ENTIRE unchanged frozen Arithmetic156 theorem and author proof, including every smooth connected projective fourfold X with nonempty smooth connected divisor D, the order-two root stack convention, all four numbered items, the enlarged generic choice and every exclusion. Do not discover a substitute, freeze a new scope, silently repair or modify author files, weaken/rename the target, assign acceptance/count or start downstream work. Source057 AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE, including the compact abelianity theorem, the two-step monodromy manuscript and the conditional fourfold-pair manuscript with its eightfold construction, transfer proposition and submersion witnesses. Read actual source interfaces and verify applicability/new deductions, never audit source truth because the headline resolves Campana's abelianity conjecture.",
    "",
    "Exact read-only inputs, project-relative under frontier/campaigns/2026-10-14/:",
    "fresh-arithmetic-discovery-r156/FROZEN.md",
    "fresh-arithmetic-discovery-r156/FROZEN.sha256",
    "fresh-arithmetic-discovery-r156/AUTHOR-PROOF.md",
    "fresh-arithmetic-discovery-r156/DERIVATIONS.md",
    "fresh-arithmetic-discovery-r156/UNRESOLVED.md",
    "fresh-arithmetic-discovery-r156/FINAL.md",
    "fresh-arithmetic-discovery-r156/REPORT.md",
    "fresh-arithmetic-discovery-r156/private/READING.md",
    "fresh-arithmetic-discovery-r156/private/SOURCE-MAP.md",
    "discovery-arithmetic-r156-parent/assessment.md",
    "discovery-arithmetic-r156-parent/questions.md",
    "",
    "Frozen SHA256 91e62de24ee1198647e25cc0ee946b8043c480a6a975280bad046be581ed7e3c,1912bytes (FROZEN.sha256 carries the same digest); author-proof SHA256 d9c17da764f4224dd02733a09a84eba9f5c47b6a37481ab68aa9e68d6b042f3e,23878bytes. Preserve bytes AND modes. Author FINAL f54cbec3628425053feba7f617cb95e64e5bf6cdc21c164c2592413d075c4973, MANIFEST f965e1aaac429f391c81020529247a7e0f3fe960861116fa1b22ff006fdd815a, outside REPORT 4520140adda6138616c2c7be0a53cc22e966a09b4d0573515197df70ada9c599. 85 selected payload files (manifest format r156-exact-packet-v1), 3 exterior files (MANIFEST.json, REPORT.md, ANCHORS.sha256). Artifact checks are not mathematical gates.",
    "",
    "Exact author metadata exceptions under fresh-arithmetic-discovery-r156/: MANIFEST.json, ANCHORS.sha256, private/{authentication.json,tree-selection.json,source-reading.json,completed-reads.json,history-reading.json,history-sections.json,history-local-topology.json,history-search.json,guards.json}; actual exact private/primary acquisition/version records (acquisition.json, acquisition2.json, abkp-acquisition.json) listed in that manifest. These metadata may identify further EXACT source/primary/copied-original bodies and ORIGINAL history intervals needed for independent operative reading, not their containing namespaces broadly. Authenticate/read the actual complete canonical and operative primary proofs and original-history sections before extended review conclusions. Recorded semantic extents are attributed author claims, not YOUR reading. New downloads/copies/extracts/renders/notes stay ONLY under private/ inside YOUR exclusive root. Do not read any other arithmetic156 role/parent adoption/status/activity/finding, or any Arithmetic157/Structural189 body/status/summary. Preserve all older scopes.",
    "",
    "No catalogue traversal. If needed ONLY binary seek/read sources/CONTENTS.md[101052,103503), Source057. Complete-tree metadata13223/nontruncated is the path authority. Three canonical manuscript folders, forty-two tree blobs (12/15/15): The-abelianity-conjecture-for-special-compact-Kahler-manifolds-September-23-2026 (wrapper build/paper.tex,1652bytes/blob0e894f3d2a5b2b8653d94b896cf75f0cf731d6b7), Two-step-monodromy-of-special-quasi-projective-varieties-September-24-2026 (wrapper build/main.tex,2651bytes/blob05e3fb672239d47fc0d68cb01f137f46091195ad), A-conditional-abelianity-theorem-for-special-fourfold-pairs-with-a-half-weight-divisor-October-5-2026 (top-level build/source/main.tex,1206bytes/blob8a7e0a0e12e583b341c4bb3ea50e538e679a8889 and build/source/inertia.tex,1207bytes/blob850838281e66b966b384c2197d07274e04b9fa27). All operative TeX bodies and includes used by the author proof must be read; the author reports 36 of 42 objects completely read, with the three compiled PDFs and inertia-descent/foundations/minimality.tex authenticated only. The source special eightfold with its surjection pi1(Y)->pi1(R), items (2)-(4) consequences, prop:transfer and the ordinary/root-chart submersion witnesses are PAID in their actual hypotheses.",
    "",
    "Frozen scope in full: X smooth connected complex projective fourfold, D nonempty smooth connected divisor, R=sqrt[2](X,D) the order-two root Deligne-Mumford stack with pi1(R) the topological stack group, equivalently pi1(X minus D) modulo the normal closure of squares of all D-meridians. There exist a smooth connected complex projective eightfold Y and a representable f:Y->R with coarse composite g:Y->X such that (1) f induces an isomorphism pi1(Y)->pi1(R) up to base-point conjugacy; (2) the smooth general fibre of g is a product of four smooth connected genus-one curves, hence has trivial cotangent bundle; (3) there is an effective Cartier E with g^*D=2E, g is submersive at some point over a general point of every prime divisor of X other than D, and f has a submersive local lift to the root chart over a general point of D; (4) if R is special in the fourfold-pair source's differential-line sense then Y is Campana-special. Y may be chosen by the source four-factor diagonal-quadric construction with sufficiently high base twist and a general coefficient tuple additionally satisfying the author's curve conditions. Read FROZEN bytes for every convention. No uniform degree, index, polarization, canonical choice, simultaneous relative construction, finite/etale manifold uniformization, or assertion for other root orders, boundary configurations or dimensions is claimed. Items (2)-(4) are source consequences retained through the enlarged choice; item (1) upgrades the source surjection to an isomorphism.",
    "",
    "Claimed new operations: one-factor integral stack Lefschetz on the root orbicurve combined with the primitive two-node I2 contraction relation (killing delta, not merely 2delta); transport of each killing thimble through the other three smooth factors over a detoured path in the four-factor fibre product over an aspherical cover without a global section; exact identification of the root-meridian kernel through upstairs meridians and analytic sections of the source submersion witnesses, with exceptional divisors retained. No deliberately unpaid interface is claimed inside the frozen scope; UNRESOLVED.md lists review interfaces. Parent questions are checks, not adopted defects. NO prior independent review findings or repair responses exist: this is round1.",
    "",
    "Primary coverage/limits requiring independent comparison: Halpern-Leistner arXiv 1008.0891v1 Theorem 2.5 and Corollary 2.7 (stack Lefschetz; check actual compactness/representability/positivity hypotheses and the pi1 range); Amoros-Bogomolov-Katzarkov-Pantev math/9810042v2 section 2 and Lemma 3.2 (orbifold fundamental groups of fibrations); Shimada arXiv 0906.1074v1 Corollary 1.1 and Example 3.5 (Lefschetz-type pi1 for elliptic fibrations; the author excludes its irreducible-fibre theorem as premise); Sommese and Campana bodies as acquired; the Matsumura PDF was inaccessible (HTTP 403) and is not used. Check actual strongest primary proofs for YOUR role; inaccessible, partial or indirect references are limits, not evidence for a favorable grade. Forty-three original-history sections among 1731 eligible files (40 lexical, 3 local-topology) were read by the author with disclosed false admissions and coarse omissions; exact extents are in the private history records. Older orbifold/root-stack/fundamental-group/special-variety/elliptic-fibration targets remain unchanged.",
    "",
    "Arithmetic147, S183N, S182P, Analytic161/T337A161 and T366A166 are whole-scope PASS/TECHNICAL, correctness conditions DISCHARGED, ZERO count; no bodies admitted. S176A remains correctness INCOMPLETE and contribution TECHNICAL conditional on full correctness, condition UNDISCHARGED. T054L136 remains UNRESOLVED_FULL_SCOPE_REPAIR. Arithmetic148-155, Structural184-188 and Analytic177 remain PREFREEZE/no nominee at their exact unpaid bridges; no body beyond the exact admitted author inputs is allowed. No prior target is reopened, weakened or regraded.",
    "",
    "Write full independent REVIEW with derivations and exact entire-scope verdict, every unresolved obligation if any, own reading-and-isolation record, outside REPORT, FINAL, YOUR OWN exact selected manifest and read-only explicit-anchor verifier. Seal once with detached FINAL/MANIFEST/REPORT hashes and proportionate tiny COPIED controls. Do not attach inherited author manifest to a reduced review selection. Protected source/primary/history/copied/rendered bodies and named metadata stay private/local and unstaged. No nested agents, author/shared/git changes, public actions or downstream work. Parent alone integrates and adopts grades/counts.",
    "",
]
standing = s189[55:]
assert standing[0].startswith("--- COMPLETE ORIGINAL STANDING BRIEF")

out = {}
for role, title, root, rp in (
    ("proof", "Arithmetic156 — independent proof review, round1.", "arithmetic-r156-proof-r1", role_proof),
    ("contribution", "Arithmetic156 — independent contribution review, round1.", "arithmetic-r156-contribution-r1", role_contrib),
):
    lines = [title, f"Write ONLY frontier/campaigns/2026-10-14/{root}/."] + header + ["", rp, ""] + common + standing
    text = "\n".join(lines)
    for bad in ("arithmetic-r147", "Arithmetic147 —", "arithmetic147 review role", "Source048", "Source313", "S183N contribution review", "structural189 namespace remains", "Structural discovery r189", "K(n)-local sphere", "fresh-structural-discovery-r189"):
        assert bad not in text.replace("Arithmetic147, S183N", ""), (role, bad)
    assert "*arithmetic*r156*" in text and "*arithmetic*r157*" in text and "*structural*r189*" in text
    other = "contribution" if role == "proof" else "proof"
    p = ET / f"arithmetic-r156-{role}-r1-brief.txt"
    assert not p.exists()
    p.write_text(text)
    data = p.read_bytes()
    out[role] = {"path": f"expanded-target-2026-10-17/{p.name}", "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data), "lines": len(lines), "output": root}
print(json.dumps(out, indent=1))
