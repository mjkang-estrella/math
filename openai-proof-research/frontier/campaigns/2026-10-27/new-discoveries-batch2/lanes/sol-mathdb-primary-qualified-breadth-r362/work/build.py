from pathlib import Path
import json,hashlib,datetime,math
from fractions import Fraction
R=Path(__file__).resolve().parents[1];L=R.parent
rows=json.loads((R/'records.json').read_text())
text='''405899|deep_algorithmic|Uniform deterministic worst-case linear time in the comparison pointer-machine model is the substantive MST complexity gap; randomized or inverse-Ackermann algorithms do not meet its quantifiers. No new comparison mechanism.
318636|park_no_uniform_mechanism|Primary Conjecture 3.17 requires a degree-multiset-preserving bijection of all trees for every permutation; a bound on the sum does not produce this matching. Source already checks r<=7. No new all-r Hall/injection mechanism.
319476|known_refutation_primary_checked|Literal record says refuted. Primary Conjecture 1 and Section 4 describe the variance counterexample and Markovian extension; there is no new target here. Only selected sections read, not all proof dependencies validated.
320716|park_source_scope_needed|A threshold uniform across admissible precoders requires the exact outage model, domain and channel law. Scalar special cases and numerical optimization do not establish all matrix dimensions or uniqueness; no certified violating channel.
325506|deep_extremal_framework|The universal forbidden-matrix exponent upper bound is the Anstee-Sali framework, overlapping 335587 after exponent convention shift. Product constructions only supply the existing lower bound; finite F cases are not the full target.
335587|deep_duplicate_framework|Same full forbidden-configuration exponent framework as 325506, with largest-avoiding-product exponent rather than smallest-forcing exponent. No general upper-bound mechanism; single forbidden matrices would not resolve universal scope.
335702|park_asymptotic_probability|Both all-K positive liminf for negative stabilization time and positive probability of never changing leader require Condition II-tau and infinite-time control. Finite coalescent simulations cannot certify either; no coupling giving these events.
341524|routine_full_scope_derivation_uncredited|Primary v1/v3 Conjecture 1 Eq33 concerns the optimal number of simultaneous links, not retransmissions. Conditional uniform radial order statistics give the full shifted-Poisson law by a standard gamma integral; preserved in ordinary-proof.md for review. Routine adaptation and incomplete prior screen prevent credit. Moment typo is separately uncredited.
342519|park_structural_combinatorics|Endpoint forests must force every interval vertex graph to be a forest for arbitrary permutations. Literal repeated-v notation is a transcription issue, not a novel counterexample. No structural propagation proof or genuine interior obstruction retained.
343970|deep_ring_extension|Arbitrary division-ring embeddings and arbitrary prescribed blocks require compatible division-ring extensions; small-n constructions are already partial results. The statement implies a pure-semisimplicity consequence; no universal amalgamation mechanism.
355935|park_source_scope_needed|Equality of two five-parameter regimes requires the exact isotropic optimization theorem in every dimension and the two power-control regions. A scalar Gaussian comparison or local Hessian does not prove set equality; no full parameter witness.
357356|famous_hard_equivalent|Explicitly equivalent to the full Lonely Runner conjecture for all positive primitive distinct velocity vectors. Geometric rewriting and fixed dimension checks provide no new all-dimensional mechanism.
365659|deep_prime_tuple_primary_checked|Primary Conjecture 1.2 and Sections 4-5 reduce attainment to simultaneous primes such as 12t+5,3t+1,2t+1. Bateman-Horn conditional result is already Theorem 1.3; million-prime searches and unconditional larger bounds do not prove infinite attainment.
365716|park_generic_dynamical_limit|Arbitrary Q,K and every diagonalizable positive-simple-spectrum V with almost-every initial configuration require global dynamical exclusion of non-antipodal limiting behavior. First-token convergence or identity V is insufficient; no positive-measure counterexample or triangular Lyapunov mechanism retained.
370654|known_refutation_record_only|Literal statement explicitly says the cited paper constructs a counterexample. Reject as already reported refuted; no claim to have read its primary construction or established dimension and dependencies.
370763|park_integral_geometry|Exact Crofton identity for every Lagrangian K and a scalar conformal metric is stronger than two-sided bounds. Requires actual law-defining datum and tangent-plane intersection kernel; no admissible anisotropic datum witness retained. Simulation is not proof.
373910|park_infinite_joint_law|Equality of the entire point-process law for every a>=0 is much stronger than one top-point marginal. Exponential-gap simulations and the a=0 largest-point case cannot resolve joint distributions; no generator intertwining established.
374578|park_rigidity|A finite set of surface subgroups must determine every admissible Kahler-Einstein metric up to identity-homotopic isometry. Finite-dimensional heuristic alone gives no global injectivity; source-specific subgroup and area definitions needed.
374987|known_refutation_record_only|Literal record already reports repeated roots for all k=14h-1 and 30h-1 and k=13 smallest. Finding another repeated root would duplicate reported refutation. Primary proof not read.
381055|park_definition_fidelity|CNC/CNA definitions and conditional/external-field quantifiers must be recovered from primary text; the literal rendition is visibly corrupted and conflates event and coordinate conditions. Exploiting wording is ineligible; no actual urn counterexample.
381640|known_resolution_record_only|Literal record reports four parts confirmed and a published counterexample addressing remaining claims. No new full six-part target established; source counterexample not independently read or replayed.
384617|deep_influence_inequality|All n and all Boolean-cube real functions with a polynomial-in-degree constant is a stronger Aaronson-Ambainis influence problem. Parseval only supplies dimension-dependent control; no degree-only replacement.
384619|deep_semigroup_tail|All dimensions, all spectral tails and all times with a degree-linear Lp exponential rate is a dimension-free analytic assertion. The p=2 spectral theorem is routine and does not settle arbitrary p.
384620|deep_tail_inverse_bound|Requires uniform lower bound d*c_p on the cube-tail generator for every dimension. L2 eigenvalue control or a constant depending on d is insufficient; no dimension-free inverse multiplier bound.
384621|wording_not_credit|Literal ordinary-monomial tail is not a Hermite spectral tail: even monomials have a nonzero mean, obstructing decay to zero. This exposes a basis/transcription ambiguity; no credit for refuting that wording and no solution of intended Gaussian tail assertion.
384622|park_gaussian_scope|Need resolve whether Lin{x^k:k>=d} denotes Hermite chaoses and fix sign convention N=Delta-x grad. A literal-basis shortcut would be a wording issue; no all-dimensional Gaussian inverse estimate for intended spectral tail.
384624|deep_degree_growth|The substantive request is one exponent C polynomial in d across dimensions, not merely finite constants for a fixed d. Standard degree-dependent Bohnenblust-Hille bounds do not supply polynomial growth.
384625|deep_homogeneous_degree_growth|Homogeneous restriction still asks for polynomial-in-degree Bohnenblust-Hille constants uniform in dimension. Fixed d or a single monomial is routine; no mechanism controlling all homogeneous coefficient arrays.
384631|park_set_theory|Implication from a non-sigma-finite Hausdorff-measure pathology to failure of Borel conjecture requires gauge quantifiers and set-theoretic hypotheses. No definable countermodel or implication construction; finite examples cannot address it.
385040|deep_with_wording_defects|Full symmetric log-Brunn-Minkowski inequality is the real target. Literal equality description omits homothetic examples and endpoint cases; these are wording defects and receive no discovery credit. No full inequality proof.
385041|deep_brunn_minkowski|Uniform all-p>=0 symmetric-body statement includes the p=0 logarithmic problem. Classical p>=1 results or one-dimensional examples cannot resolve it; no new convexity mechanism.
386245|park_missing_chain_definition|Two mixing-time scales depend on a nonreversible transition rule absent from the literal record. Graph connectivity or shortcut counting alone cannot prove those chain-specific estimates; primary model needs recovery before a witness.
387366|park_graph_limit_invariant|Cost compares infima over uniformly bi-Lipschitz rewirings, while local weak convergence alone controls fixed-radius statistics. No pair of bounded-degree graph sequences with rigorously separated costs or general transfer argument constructed.
387659|likely_classical_no_cheap_route|Arbitrary real nonlinear P with at least deg(P)-1 nonreal zeros of P^2+P' is a real-root-distribution theorem, not just the real-rooted-P special case credited in the record. Classical solution lead requires primary successor check; no novelty claim or certificate.
387794|park_missing_product_parameters|The definition of tensor/convolution product and r in terms of p,q is deferred to Problem 6.44. Coefficient experiments without that source definition cannot certify a quasiconformal-extension counterexample.
387891|known_theorem_lead_unverified_primary|Semiadditivity of analytic capacity is a classical Tolsa theorem lead and would subsume this constant-M question. No primary theorem body retrieved here: mark known-result lead, not completed proof/prior clearance; re-proving it is not low hanging new work.
387928|park_capacity_extension|Question involves continuous analytic capacity on E minus K, possibly noncompact, with exact invariance for every zero-capacity compact K. No legitimate deletion theorem or analytic-capacity identification verified; smooth-arc cases do not give all compact K.
388001|deep_matrix_discrepancy|Matrix Spencer asks an O(sqrt n) signing for n arbitrary noncommuting norm-one symmetric n-by-n matrices. Scalar/commuting cases and standard sqrt(n log n) estimates are insufficient.
388004|deep_probability_tail|Sharp Feige tail bound concerns arbitrary independent nonnegative mean-one variables and all n. Markov gives only n/(n+1), not the required universal 1-e^-1; no extremal-law reduction or violating law retained.
388439|park_ergodic_scope|Simultaneous rationally independent polynomial iterates with separate T_i need exact commuting/measure-preserving system assumptions from primary source. Single-transformation recurrence or finite cyclic samples do not prove this multi-transformation lower bound.
388566|deep_complex_dynamics|Uniform geometry across every depth and tuning index requires quantitative complex renormalization control, not merely finitely many input polynomials. No modulus bound uniform under iteration supplied.
389177|deep_diophantine_nonexistence|All six exceptional D(n) parameters require ruling out every positive integer quadruple. Modular obstructions or bounded searches do not provide full simultaneous nonexistence; no new descent or Pell incompatibility mechanism.
389482|park_missing_axioms|Numbered SIRSN properties and geodesic axioms are absent from record. Four implications require source definitions before constructing a model; no valid implication proof or invariant random network counterexample.
389880|incomplete_object_definition|The group G is not defined in the literal excerpt. Automorphism rigidity cannot be evaluated without recovering ambient-space/group structure; no credit for treating an arbitrary G as the intended knot-theoretic object.
392775|known_theorem_record_only|The literal statement is already explicitly Theorem 6, including associativity and Hamiltonian comparison. Database open label does not create a new question. Primary proof and definitions not read.
393359|known_refutation_record_only|Literal record says a type II_1 Arveson-system counterexample is constructed in the report. Already reported negative answer; no claim to have read the complete construction.
396099|vague_quantitative_target|How many samples and overwhelming probability lack fixed epsilon, probability and n asymptotic conventions. Existing covariance concentration results are relevant, but no precise new sharp target or source theorem body isolated.
396247|park_operator_stability|Characterizing amenability by uniform approximate-representation stability plus local unitary conjugacy is an all-discrete-groups structural question. Finite-group averaging does not address arbitrary nonamenable groups; exact moduli needed.
398345|famous_hard_saw|Nontrivial polynomial displacement exponent gaps in dimensions two and three require uniform self-avoiding-walk estimates. Finite walk enumeration cannot establish an asymptotic exponent gap; no new lace/geometric mechanism.
398358|deep_diophantine_progressions|For every nonlinear integer polynomial, an f-dependent finite bound must exclude arbitrary long progressions in its integer-value set. Squares or fixed progression lengths do not settle all degrees; no uniform Diophantine obstruction beyond known examples.'''
D={}
for line in text.splitlines():
 i,c,r=line.split('|',2);D[int(i)]=(c,r)
assert set(D)=={x['mathdb_id'] for x in rows} and len(D)==50
primary={318636:['sources/trees.pdf','sources/trees-v2.pdf'],319476:['sources/localvol.pdf'],341524:['sources/mmwave.pdf','sources/mmwave-v3.pdf'],365659:['sources/subgroups.pdf']}
out=[]
for x in rows:
 n=x['mathdb_id'];c,r=D[n]
 out.append(dict(mathdb_id=n,title=x['title'],canonical_url=x['canonical_url'],literal_statement=x['statement'],literal_statement_sha256=hashlib.sha256(x['statement'].encode()).hexdigest(),disposition=c,individual_reason=r,evidence_level='primary_statement_and_selected_body_sections' if n in primary else 'literal_corpus_statement_only',primary_body_review=n in primary,primary_sources=primary.get(n,[]),concluding_proof_section_read=n==319476,full_resolution_proof_body_read=False,complete_dependencies_read=False,mathematical_evidence='Full ordinary derivation retained, unreviewed and uncredited' if n==341524 else 'Screening obstruction/known-result lead only; no new full proof',source_scope_cleared=False,prior_cleared=False,novelty_evidence='No novelty clearance; open label and empty solutions disregarded',accepted_credit=0))
(R/'dispositions.json').write_text(json.dumps(dict(dispositions=out),indent=2,ensure_ascii=False)+'\n')
(R/'proposals.json').write_text('[]\n')
# Exact finite algebra cross-check of Gamma tail differences, not the all-N proof.
checks=[]
for N in range(1,33):
 a=[Fraction(1,math.factorial(j)) for j in range(N)]
 b=[Fraction(1,math.factorial(j)) for j in range(N-1)]
 diff=[a[j]-(b[j] if j<len(b) else 0) for j in range(N)]
 assert diff==[Fraction(0)]*(N-1)+[Fraction(1,math.factorial(N-1))]
 checks.append(dict(N=N,coefficient=str(diff[-1]),pass_exact=True))
(R/'bounded-checks.json').write_text(json.dumps(dict(description='Exact rational verification of gamma survival difference polynomial for N=1..32; supplemental only, no Monte Carlo or finite-to-universal inference',checks=checks),indent=2)+'\n')
# Freeze all actually consulted upstream inputs, flat only.
bindings=json.loads((R/'input-bindings.json').read_text());seen={e['path'] for e in bindings}
ps=[L.parent/'ledger.json',L.parent/'prior-campaign-context.json',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md'),L.parent/'AGENTS.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']
for p in ps:
 if str(p) not in seen:
  b=p.read_bytes();bindings.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(R/'input-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
# Retain literal extracted statement sections with PDF/version and line locator.
sections=[('mmwave-v3',940,1100),('trees-v2',940,1000),('subgroups',1,80),('subgroups',250,275),('localvol',98,120),('localvol',290,395)]
with (R/'primary-excerpts.txt').open('w') as f:
 for n,a,b in sections:
  f.write(f'\nSOURCE sources/{n}.pdf; pdftotext -layout work/{n}.txt lines {a}-{b}\n')
  f.write('\n'.join((R/'work'/f'{n}.txt').read_text().splitlines()[a-1:b])+'\n')
print('50 dispositions; 4 primary statement/body screens; 0 eligible proposals; 32 exact algebra checks')
