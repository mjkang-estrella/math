# R144 frozen author-proof scope: conditional finite-rank truncation

Status: author-proof nominee scope; no correctness, contribution, acceptance, or count assignment. Publication remains STOPPED. This is not the r114 Borel packing/covering target and has no pair, self-duality, or packing/covering conclusion.

Work in ZFC. Let M be ANY finitary matroid on a countably infinite ground set E. Let T be ANY M-independent set such that T is infinite and the contraction M/T has infinite rank. Let (E_n)_(n>=1) be ANY increasing sequence of finite subsets with union E. Relative rank is r_M(A|X)=r_(M/X)(A minus X). For every M-independent X define

    q_n(X)=r_M(E_n|T)-r_M(E_n|X),
    ell(X)=liminf_(n->infinity) q_n(X) in Z union {-infinity,+infinity}.

Claim. The family

    I_N={X in I_M : ell(X)<=0}

is the independent-set family of a matroid N on E. Its bases are EXACTLY

    B_N={X in I_M : ell(X)=0}.

N is a generalised truncation of M in the precise sense: I_N subset I_M, and whenever I is N-independent but not an N-basis and e is outside I with I+e M-independent, I+e is N-independent. Every finite M-independent set is N-independent; thus the finitarization of N equals M. Every N-basis is infinite and has infinite relative corank r_M(E|B). In particular T is an N-basis, N differs from M and from every integer truncation of M, and N is a wild generalised truncation (this use of wild means the truncation definition, not an unasserted circuit-cocircuit property).

In the Cantor topology on 2^E, I_N is Pi^0_3 and B_N is Borel. All assertions hold simultaneously for each M,T,(E_n) as quantified above; no Martin's Axiom, CH, representability, local finiteness, effective presentation, or additional hypothesis is imposed.

Consequently every countable finitary matroid of infinite rank has such a Borel wild generalised truncation: split a countably infinite basis into two infinite parts and take one for T.

Not claimed: arbitrary uncountable grounds; simultaneous prescription of an arbitrary collection of strong-equivalence classes; self-duality; an infinite matroid packing/covering counterexample; a Borel selection of all interval interpolants; optimal descriptive complexity; independence from the chosen exhaustion; current-open or worldwide-priority status.

Prefreeze basis: notes/02-rank-probe-prefreeze.md records the exact finite-support and decreasing-limit construction before this freeze. Since that note, the full Bowler–Geschke author-version MA construction (text219–386) and complexity proof (387–497, plus displayed continuation) were read, and source185 local-bases.tex reread in full. The nontrivial universal step claimed here is transporting finite conditional ranks across arbitrary independent intervals, with exact finite supports and a global integer zero level, then establishing maximal extension in arbitrary restrictions. Source185 supplies the decreasing-stage interpolation pattern; it is not being renamed as a new lemma. Gollin–Joo v1 supplies the strongest read generalized-truncation comparison, including its actual MA proof and basis criterion.
