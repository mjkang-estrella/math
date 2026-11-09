from pathlib import Path
import json,hashlib,re,datetime
l=Path(__file__).resolve().parent.parent
before=json.loads((l/'inputs-before.json').read_text())
after={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in before}
(l/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
changed=[p for p in before if before[p]!=after[p]]
(l/'logs/input-hash-check.json').write_text(json.dumps(dict(files=len(before),identical=not changed,changed=changed),indent=2)+'\n')
assert not changed
r=json.loads((l/'logs/resources.json').read_text())
build=json.loads((l/'build/logs/build-result.json').read_text())
rows=json.loads((l/'logs/sanity-results.json').read_text())
examples=sorted((l/'logs').glob('examples-*.log'),key=lambda p:p.stat().st_mtime)[-1]
checker=sorted((l/'logs').glob('checker-examples-*.log'),key=lambda p:p.stat().st_mtime)[-1]
sim=sorted((l/'logs').glob('simulation-*.log'),key=lambda p:p.stat().st_mtime)[-1]
assert 'error:' not in examples.read_text() and 'exception' not in checker.read_text()
assert 'PASS: 16 natural and 4 signed' in sim.read_text()
for endpoint in ['mathdb_338887','recurrent_count_depends_only_on_gcd']:
 assert f"'ChanLevine.{endpoint}' depends on axioms: [propext, Classical.choice, Quot.sound]" in examples.read_text()
p=l/'REVIEW.md';s=p.read_text()
s=s.replace('## C. Independent semantic sanity — PENDING\n\nOwn scripts and examples are retained in `scripts/sanity.py` and `build/formal/FidelityExamples.lean`. Results will be recorded after the serial build. Numerical checks are diagnostics, not the proof.', '''## C. Independent semantic sanity — PASS

My new `scripts/sanity.py` constructs every vertex-labelled state and every source legal advance-then-move edge, then computes terminal strongly connected components by an iterative two-pass graph algorithm. It does not use the cycle test to select recurrent states. The fixed-level natural state space is finite and forward closed; Definition 5.2 holds precisely on terminal SCCs admitting an edge. If a state shares a descendant with such a recurrent state, that descendant is inside its terminal SCC and reaches it, even when the other state is signed and outside the enumerated space. Conversely a nonterminal SCC reaches a downstream terminal SCC and cannot return. Thus this is a definition-level diagnostic.

For all 16 cases n = 3..6, m = 1..4, terminal SCC counts agree exactly with an independent integer implementation of the Lucas-trace/denominator/Ramanujan formula used in the proof. They also agree configuration by configuration with the literal facing-pair/Hamiltonian CycleTest. Each case has exactly n recurrent SCCs, each of constant weight, with distinct weights. Every vertex has a legal internal edge in each terminal SCC, permitting a diverse repeated walk. Four additional forward-closed signed enumerations with chips ≥ −1 (n = 3,4 and m = 1,2) have exactly the same recurrent counts and no recurrent negative state. All checks passed. The complete outputs, not only a few sample values, are in `logs/sanity-results.json` and the simulation log.

My `build/formal/FidelityExamples.lean:5–25` checks a canonical configuration on C₃, all three chips and rotors, its level and weight, the target of firing 0, the resulting chip/rotor values, a legal Step and conserved weight. The finite tests use kernel `decide` after unfolding CycleTest. Literal recurrence itself has unbounded quantifiers, so that example invokes the proved Sem5 bridge, not a purported decision procedure. Membership in the actual component uses Related reflexivity. Further examples cover the last residue on C₆, residue zero, and an equal-gcd endpoint application. Strict compilation and leanchecker passed.

Initial reviewer-only example runs exposed driver/root-path and PATH mistakes and the need to unfold CycleTest for its decidable instance. Those failures are retained in separate logs; they did not expose a packet theorem defect. Numerical checks remain diagnostics, not the general proof.''')
s=s.replace('## D. Bounded formal spot check — PENDING\n\nThe fresh serial import-closure build and leanchecker run is in progress. Root\'s decisive replay is separate.',f'''## D. Bounded formal spot check — PASS

The entire local import closure of ChanLevineFinal, **54 modules**, was freshly compiled from the bound sources and independently checked with leanchecker, serially. All passed; no borrowed local oleans were used. The 21 packet modules outside that closure were source-scanned, not rebuilt in this review. `build/logs/build-result.json` gives the complete order, source hashes and the 108 individual compile/checker logs. Peak reported RSS was {r['max_reported_rss_kib']:,} KiB, below the cap. The reviewer examples also passed strict compilation and leanchecker.

Both endpoints print exactly `[propext, Classical.choice, Quot.sound]` in the fresh endpoint compile log and again in `{examples.relative_to(l)}`. The endpoint itself passed leanchecker. No residual obligation or extra axiom occurs in these printed dependency lists. Root's decisive replay is separate; this review does not replace or claim it.''')
s=s.replace('Full individual logs and receipts are retained.', 'Full individual logs and receipts are retained; no build, checker or simulation process remains running.')
s+=f'\nFinal input check: all {len(before)} bound input files are unchanged. Before/after JSON manifests are identical by content. Final gates: A PASS; B PASS; C PASS; D PASS; E QUALIFIED_PASS. No acceptance or credit is assigned.\n'
p.write_text(s)
result=dict(mathdb_id=338887,role='INDEPENDENT_FORMAL_FIDELITY_REVIEW_NOT_ACCEPTANCE',date_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),self_accepted=False,credit=0,root_decides=True,
 archive=dict(path=str(l.parent/'chanlevine-assembly-r1/chanlevine-assembly-source.zip'),sha256='9e685235e4d744adf9fdd5cafaccf874c6ef6fbccff4684003133df75da34bb0'),
 gates={
 'A':dict(verdict='PASS',references=['build/formal/Dynamics.lean:18-36','build/formal/SourceSemantics.lean:28-54','build/formal/Cardinality.lean:28-68','build/formal/ChanLevineFinal.lean:11-27'],notes=['Literal signed recurrence, legal component, diverse walk and actual Nat.card count; proved nonnegativity and finiteness; component-set uniqueness proved.','Exact unique-existence predicate uses recurrent natural representatives; full converse for arbitrary diverse recurrent components is not an extra theorem in this packet. See REVIEW.md precision boundary.']),
 'B':dict(verdict='PASS',remaining_props=[],references=['build/formal/ChanLevineFinal.lean:17-20','build/formal/SemFinal4.lean:5-8','build/formal/CountFinal5.lean:4-8','build/formal/CountR7CFinal.lean:9-29','build/formal/CountR7TFinal.lean:17-35'],notes=['All seven Props discharged, including both final counting identities.']),
 'C':dict(verdict='PASS',natural_cases=16,signed_cases=4,formula_mismatches=0,cycle_test_mismatches=0,own_lean_examples='build/formal/FidelityExamples.lean',logs=[str(x.relative_to(l)) for x in [examples,checker,sim]],results='logs/sanity-results.json'),
 'D':dict(verdict='PASS',fresh_local_closure_modules=54,strict_compile_pass=True,leanchecker_pass=True,packet_modules_source_scanned=75,source_token_hits=[],axioms=['propext','Classical.choice','Quot.sound'],build_result='build/logs/build-result.json',resources=r,root_decisive_replay_claimed=False,independent_full_declaration_flag_audit_claimed=False),
 'E':dict(verdict='QUALIFIED_PASS',references=['REVIEW.md, E.1-E.8','../expanded-corpus-r127/outputs/338887-proof.md:43-57'],notes=['Manuscript must supply both statement forms, proved uniqueness, definitions/correspondence, trace collapse and arithmetic orbit, audit scope and AMS access limits.'])},
 required_fixes=[dict(scope='manuscript',item='Replace citation of unproved uniqueness with the proved sink-normalization argument or a complete source torsion argument.'),dict(scope='manuscript',item='Correct source section citation from 3.5 to 3.6 at candidate proof line 43.'),dict(scope='manuscript',item='Complete REVIEW.md E.1-E.8, including exact formal unique-existence predicate and access/audit limits.')],required_lean_endpoint_fixes=[],optional_strengthening=['Package the full equivalence between diverse recurrent components and components admitting recurrent representatives.'],
 input_binding=dict(before='inputs-before.json',after='inputs-after.json',files=len(before),identical=not changed,receipt='logs/input-hash-check.json'),
 process=dict(child_agents=False,git=False,network=False,browser_tabs=False,external_messages=False,uploads=False,shared_ledger_edits=False,writes_outside_lane=False,heavy_processes_serial=True,background_processes_left=0),
 limitations=['AMS 2022 full body not freshly accessed.','No new novelty or significance adjudication.','Only the 54-module endpoint closure was freshly rebuilt, not all 75 packet modules.','Source token scan and endpoint axiom checks are independent; assembly full declaration/metadata audit was read, not rerun.','Root acceptance and decisive replay remain separate.'])
(l/'review.json').write_text(json.dumps(result,indent=2)+'\n')
print('Finalized review: unchanged inputs',len(before),'gates A-D PASS, E QUALIFIED_PASS')
