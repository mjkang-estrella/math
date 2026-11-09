from pathlib import Path
import json,re,hashlib
D=Path(__file__).resolve().parents[1];R=D/'gate1-extracted/receipts'
r=json.loads((R/'replay.json').read_text());assert r['status']=='PASS'
log=(R/'build-ReviewerAudit.log').read_text();decls=[]
for chunk in log.split('AUDIT ')[1:]:
 name,rest=chunk.split('\n',1)
 if not re.match(r'MathDB364205\.',name):continue
 origin=re.search(r'ORIGIN (.*?)\nTYPE ',rest)[1]
 typ=rest.split('\nTYPE ',1)[-1] if '\nTYPE ' in rest else rest.split('TYPE ',1)[1]
 typ=typ.split('\nBODY ',1)[0]
 axs=re.search(r'AXIOMS \[(.*?)\]',rest)[1]
 decls.append(dict(name=name,module_origin=origin,full_type=typ,body_present=True,unsafe=False,partial=False,transitive_axioms=[x for x in axs.split(', ') if x]))
assert len(decls)==33
(D/'declaration-audit.json').write_text(json.dumps(decls,indent=2)+'\n')
bind=json.loads((D/'frozen-before.json').read_text());assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest()==h for p,h in bind.items())
report=dict(verdict='PASS',role='Independent technical reviewer, not author; no acceptance authority',gate=1,local_declarations=33,full_generated_included=True,strict_flags=['-j1','-DwarningAsError=true'],allowed_axioms=['propext','Classical.choice','Quot.sound'],module_replay=r,objections=[],negative_control_scope=['Rejects false A.card = 32 by decide','Rejects distance zero between opposite signed vertices of Q1 by decide'],source_semantics='PASS: source Section 2 exact diameter, outside maximality, every-member diameter partner; Section 6 Conjecture 1, all n,r with r<=n. Positive witness (8,5) independent of zero conventions.',frozen_files=len(bind),trust_limit='Pinned compiler and prebuilt external dependencies trusted. No upstream rebuild/source-to-olean attestation; collectAxioms uses exported imported-dependency metadata.',accepted_credit=0)
(D/'technical-review.json').write_text(json.dumps(report,indent=2)+'\n')
(D/'TECHNICAL-REVIEW.md').write_text('''# Gate 1: independent strict Lean technical review

**PASS, within the stated trust boundary.** I reviewed the author packet as an independent technical reviewer, not its author. This report is separate from the manuscript and does not accept a campaign result. Zero accepted credit; root alone accepts; administrative count remains 7/20 beyond 39 unchanged.

## Extraction and proof checks

The frozen hash baseline was taken after initial orientation reads and before any extraction, independent computation or replay; that timing is explicitly disclosed. The author source-only ZIP was safely extracted into gate1-extracted after rejecting absolute/traversal/symlink members. Cube.lean and Signed.lean match the frozen author bytes. The independent driver in scripts/replay.py, rather than the author driver, strictly rebuilt every positive module using lean -j1 -DwarningAsError=true and separately ran leanchecker for each. The original Audit, Inventory and Safety diagnostics are also built. Receipts under gate1-extracted/receipts record command lines, exits, timing, total VmRSS, private RSS, and systemd MemoryMax enforcement. All final commands passed; no resource cap was reached.

ReviewerAudit enumerates declarations by module origin, not merely a hand-written name list or namespace prefix. It checks all 33 Cube/Signed declarations including four generated sign-equivalence proof auxiliaries and signedA.eq_1. For each it records the full type with pp.all/pp.universes, actual value? true body presence, module origin, unsafe and partial flags, and transitive axioms. declaration-audit.json retains the structured result and the raw full output remains in the log. Every body is present; no local axiom, unsafe or partial declaration occurs. Dependencies are subsets of propext, Classical.choice and Quot.sound. The mathematical sources contain no sorry/admit/axiom/unsafe/native_decide/ofReduceBool. Imported external oleans and the pinned Lean binary are trusted; this is not an upstream rebuild or independent source-to-olean attestation. collectAxioms uses exported dependency metadata across module boundaries.

## Source comparison and quantifiers

I read the frozen v1/v2 primary source definitions in Section 2 and the definition of b' and Conjecture 1 in Section 6, alongside both complete mathematical modules. Source distance counts unequal sign coordinates. Boolean dist counts the same coordinates; signEquiv maps false to -1 and true to +1, proves both inverses, and cubeEquiv lifts this bijection. dist_encoding proves preservation rather than assuming it. signedA_card proves injective cardinality transport. signedA_maximal pulls an arbitrary signed outsider back to the Boolean cube and transfers an offending partner; no restricted outside list replaces full quantification.

MaximalDiameter has the all-pairs upper bound, an actual pair attaining r, and an offending member for each outside vertex. These express exactly diameter r and source maximality. ReviewerSanity additionally proves that any diameter-at-most-r superset equals the set. Rigid quantifies over every member with a partner at the exact diameter, not just some diameter pair. The IsGreatest formulation is the source's largest-cardinality claim: attainment plus an upper bound for every attainable cardinality. LiteralSourceClaim includes all natural n,r with r<=n. In the finite signed cube it matches b'(n;r)=2^r. Even if source conventions restrict to positive dimensions/radii, the same contradiction at n=8,r=5 refutes that restriction. At r=0 a singleton has exact diameter zero and is rigid, including Q0; the empty set fails attained diameter. These edge cases are independently compiled examples, not a loophole in the result.

## Sanity, negative controls and independent arithmetic

Compiled examples cover opposite signed vertices in Q2, Q0 distance, an explicit distance-5 witness, the exact-diameter conjunct, inclusion-maximality, and the singleton/empty zero-radius distinction. NegativeCard fails because A.card=32 is false, and NegativeDistance fails because opposite Q1 signs have distance 1 rather than 0. The driver requires a real Lean error, nonzero exit and no cap termination. These controls test only those false propositions; they are not a compiler soundness proof.

The independent coordinate checker in scripts/check_witness.py imports no author computation. It confirms 34 distinct vertices, ordered histogram (34,72,276,308,276,190,0,0,0), maximum 5 for every member, and maximum greater than 5 for all 222 outsiders. Its 256-row certificate is diagnostic redundancy; the kernel proof does not depend on Python.

## Objections and limits

No concrete objection to the author proof or endpoint was found. Driver-development failures are not concealed: an initial leanchecker launch lacked lean on PATH, and reviewer-only zero-radius examples needed unfolding plus a qualified distance name. These were corrected without changing Cube or Signed; available failed-attempt receipts are retained separately. The initial PDF marker invocation used a wrong relative path; the installed helper was later resolved and used before final regeneration. The first build preceded the successful marker, a procedural deviation unrelated to the Lean verdict. Novelty/significance are outside this gate; the supplied independent source review remains QUALIFIED_PASS in those dimensions. No global priority, optimum, minimality or family result is inferred.
''')
print('Gate 1 PASS')
