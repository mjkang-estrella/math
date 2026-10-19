# Source243: why a recorded-history interpreter does not flatten choices

Prefreeze feasibility only. Neither a nesting-collapse theorem nor a nesting-separation theorem was frozen or proved.

## Strongest contracts checked

Both source243 introductions were read. The noncapture paper treats a fixed eight-binary-relation vocabulary, arbitrary finite-rank HF objects, exact counting, polynomial traces and a full all-input F3 consistency query. Its companion already has one SYNTACTIC occurrence of WSC with possibly many successive choices and many parameter evaluations. It does not claim that arbitrary nesting collapses.

The companion's actual `01-formalism.tex` and `03-sentence.tex` guarded-choice/history passages were followed. The witness condition `mod:witness-condition` is

    Mi ⊆ Aut(A, parameters, b0,…,bi),
    for all u,v in Di some g in Mi sends u to v.

The bi are intermediate HF states. It is NOT a requirement to fix every ephemeral chosen element ci when that element leaves no distinction in the next state. The final-state argument of the witnessing term may be used to certify an earlier stage. Witness failure propagates as dagger rather than becoming false. The source has an explicit transitivity guard and pure dummy choice (`sen:guarded-choice`), an exact finite-tree completion test (`sen:tree-test`), and `sen:history`: current selected atoms contain each previous state and witnesses fix those atoms individually. This already pays legality on arbitrary inputs and polynomially many sequential choices in that architecture.

The actual primary is Lichter–Schweitzer [2205.14003v3](https://arxiv.org/pdf/2205.14003v3). Section3.1, Definition3, Lemma4 and Corollaries5–6 give the full-path orbit semantics. The text after these results explicitly distinguishes intermediate states from the chosen ci and preserves all earlier states. Section5.2 Definition26 makes DeepWL+WSC an inductively nested algorithm with separate subroutine clouds; a `refine` call returns a relation, not its full private history. Section5.5 Lemma61 simulates those algorithms by induction on nesting depth. Its step and witnessing terms can invoke the already constructed nested subterms. Thus this primary compiler is not a one-occurrence normalization theorem. Its concluding questions explicitly distinguish nesting from the basic CPT versus CPT+WSC separation.

## The most direct compiler and its failure

The proposed feasibility route was to simulate a fixed nested sentence with one WSC loop, using an HF stack for control, parameters, intermediate states and saved inner choices. Polynomially many operations at fixed syntax depth would give a polynomial-sized stack. Ordinary CPT iterations can be flattened this way. The question is whether the original automorphism witnesses still act on the enlarged recorded state.

A two-atom calculation prevents simply claiming they do. Let A={a,b} have no nontrivial input relations, so Aut(A)=S2. A legal inner WSC call first chooses an atom from A, stores its singleton as an intermediate state, stabilizes with a dummy choice and returns the pure Boolean true. At its first stage, the transposition of a,b witnesses the choice. At the dummy stage identity suffices. A second independent call, with no atom parameter inherited from the first, has the same legal choice from A. The returned truth values carry no chosen atom.

A direct flattened trace that records the first singleton {a} among its outer intermediate states imposes Aut(A,{a}) on every later outer witness. This subgroup is trivial for two atoms. Its orbits on A are {a} and {b}; A is not one orbit. Consequently the second intended whole-A choice has no valid transitivity witness in this interpreter. Erasing {a} from the CURRENT stack later does not erase it from the sequence of earlier outer states.

This is deliberately only a compiler diagnostic. The Boolean expression in the example is just true and has a trivial choice-free equivalent. A smarter compiler can eliminate unused calls, represent states by invariant orbit data, avoid recording distinctions, or choose a different program. No logical separation follows from the example, and no generic impossibility of flattening is asserted. Nor does it contradict the primary's observation about ephemeral ci: the failure here requires an actually recorded singleton bi.

## Attempted orbit repair

Retaining all symmetry-related versions of each inner state would avoid naming a particular first singleton. For one call this can be small. Under many successive asymmetric choices, however, the relevant object is an orbit of entire compatible histories; its cardinality need not be bounded by the polynomial size of any one run. The primary explicitly allows the set of terminal states to be a semantic object rather than an activated polynomial-sized HF set. Enumerating all histories therefore changes the resource contract. Quotienting them requires an effective HF representation and preservation of membership, exact counting, final-state witnesses, failure propagation and the original parameter stabilizers. No such polynomial-size representation was constructed.

The source's growing-selection proof cannot be inserted here: it retains every earlier chosen atom on purpose and never returns to a less individualized inner-call environment. Its lower-bound supports compare traces on specified charged structures; they are not a universal canonization or orbit-compression algorithm for arbitrary inputs.

Historical I147 was read at its actual source243 discussion and growing-individualization target. That older direction already keeps a separate marked-stabilizer/homogeneity gap; it is not a new target here. The present calculation does not claim an answer to that question either. With the history-reset compatibility unbuilt, freezing the full nesting question would repeat the problem of choosing a headline before constructing its main invariant. This screen remains an archive, with no nominee.
