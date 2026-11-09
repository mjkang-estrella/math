# 343790 continuation blueprint (state: stage1+2+3ground green, src 73b81dd9)

## Done
- codeLoopF (9-monomial), codeLoopQ, zero-normalization L/R
- zmod2 helpers: val_one, cases, mul_self, add_self, one_add (x=1+(1+x))
- codeLoopF_self / _symmetry / _coboundary -- all-input via rcases zmod2_cases cascade + decide
- W4:=Fin 4->ZMod2, W3:=Fin 3->ZMod2, e4v/e3v, dot4/dot3, add/zero lemmas
- card_W4=16, card_W3=8 (Fintype.card_pi + ZMod.card + prod_const), exists_one_of_ne_zero4

## Pin facts (empirical, r3)
- ring does NOT close char-2 coefficient goals here; pre-fold with zmod2 lemmas or decide-cascade
- ZMod 2 defeq Fin 2; ZMod.val_one 2 needs ⟨by decide⟩ instance
- Mathlib.Tactic.Omega olean MISSING in pin -- never import it (Init.Omega is in core, fine)
- Fintype.equivFinOfCardEq noncomputable (EquivFin.lean:124); Fin.sum_univ_three exists

## S3count (next)
1. card_filter_split s g : s.card = #(s.filter(g=0)) + #(s.filter(g=1)) -- ext + zmod2_cases,
   Finset.card_union_of_disjoint (alias iff, .mp takes Disjoint proof)
2. dot4_single w k : dot4 w (e4v k) = w k -- simp [dot4, e4v] + Finset.sum_ite_eq' (Piecewise.lean)
3. card_one_fiber4 hw : #univ.filter(dot w . =1) = 8 when w!=0 -- k from exists_one;
   O/Z toggle bijection a -> a + e4v k (Z.image = O via mem-grind; (x+e)+e=x by Pi.ext coord
   cases zmod2_add_self); 16 = cardZ+cardO, cardZ=cardO => 8.
4. card_one_fiber3 analog = 4 (8 = 2c).
5. parity bridge: even #s.filter(g=1) <-> sum_{s} g = 0; F2-value sub-lemma by
   s.induction (empty: 0=0; insert: zmod2_one_add rewrites 1+(1+x)).
6. even triple-fiber W4: S:={a | w1 a=1,w2 a=1,w3 a=1}, w3!=0. translate a0 in S: S~K, K even
   via K-coord-split + shift z (z != 0 in K: a0-w1-w2 combo, 3 cases) halving each class;
   K != 0: Fintype.card_le_of_injective on the triple map, 16 > 8. Even #S.
   (S is the {a : all-three-1}-fiber; used for |cap3 C| even.)
7. 4 | #(a : u a=1, v a=1) when u!=0: K1 (u-kernel) has 8, v!=0 on K1: K1 = 2x2 via v-coord
   split, halves equal by u-toggling within (u v=1 => u(a+z)=u a), each 4.
8. triple-character-sum W3: sum_{b} (x b)(y b)(z b) = the 6-monomial T. Route: expand
   product? NO -- use indicator identity + idempotence: the summand (x b)(y b)(z b) equals
   indicator of {x b=y b=z b=1} (values in {0,1}); then count parity via W3 fiber translate
   + ker argument AS IN 6 but ker may be 0: handle by T-value cases OR do the 8-fold
   cons-split sum with coefficient table c(i,j,k)=sum b_i b_j b_k: [distinct] via pair-halving
   (b_i b_j sum: {both=1} has 2 elems, F2-sum 0? NO 1+1=0 -- wait: sum of VALUES b_i b_j over
   8 elems = parity of #{both 1} = 0; triple distinct: #{all 3} = 1 odd => 1). Recommended:
   prove c-table by 3x3x3=27 finite decide after establishing sum-split lemmas; grind acceptable.
   Then sum = sum_{i j k} (x i)(y j)(z k) c(i,j,k) = T by decide-cascade (x i values).
   Fubini: Finset.sum_comm + Finset.sum_product? (verify name; else sum_fin_eq... grind).

## S4 data (43+7=50)
- H1F := univ.filter(a.3=0) erase 0 : card 8-1=7 (card_erase_of_mem), sum = sum over
  a3=0-fiber = 0 (per-coord: 4 ones by halving a j vs a j=0 within a3=0 via e j toggle
  j<3 keeps a3; bridge). H2F := {e3-analog? NO: elements (1,0,1),(0,1,1),(1,1,1) with a3=1,a2=0?
  per source: A-block {a3=1,a2=0} = 4 elems + B-block {a3=0,a1=0,a!=0} = 3 elems} explicit
  insert-finset, card 7, sum 0 by 7-term j-case decide after Pi.add_apply/simp.
- coord : W4 x Fin5 -> Fin 50 x ... actually: CD := {c : W4 x Fin5 // c.1.1 != 0 ^
  (c.1.2 = 0 or c.1.1 in H)} -- 15+4*7=43 wait: (a,t) a!=0 t any: 15*5; plus (0,t) t=0: 1?
  SOURCE PLAN: 43 = 15 + 4*7 = pairs (a,t) with a!=0 (15) + (0,t) t in {1,2,3,4}? and H-rows
  extra: a in H1: all 5 t (35+8?) -- RE-DERIVE from reviewed-implementation-plan.md before coding.
- dFun (e : Fin 50 -> ZMod2) i := sum over preimages; d from e via e.symm (Fintype.equivFinOfCardEq
  (card-eq 50)); subspace via Submodule literal; injective d via unit columns (dot with e_i).
- D_i := range d + span(e3v j as coords 39..45? simplex on B=F2^3\0 7 nonzero W3 vecs).

## S5 weights / axioms on codewords
- wt = 8 + 4h + wtS; h even; axioms 1-4 via C even-fibers + S identities (6) + q-analog on W3?
  NO -- S-part uses the SAME codeLoopF/Q on the W3 coords (x := the W3-restriction).
  ax1: |v|/4 = 2+h+wtS/4 vs q(x,x)=q(x); ax2: |v n w|/2 = q(x+y)+q(x)+q(y); ax3: coboundary;
  ax4: |cap3| parity = T via C-even + S-triple-sum (S3count.8).

## S6 loop / Moufang / nonassoc / transport / S7 classes+weights+noniso
- As in prior plan (LoopMul, 512-cascade decide for Moufang after simp reduction -- VERIFIED
  on paper that (a*b)*(c*a)=a*(b*(c*a)) reduces to coboundary identity instance);
  iso (e,p) -> (e, d_H p); classes = column-fibers; 15/7 type via H-structure;
  D1 has weight-8 word (w := e4v 3-vector as C-part, h1(w)=0 since H1 coords a3=0);
  D2 min weight 16 on C (every nonzero w hits H2: h2>=2) + 0/4 S.
- Fin50 transport: Fintype.equivFinOfCardEq both directions; permutation weight-multiset
  invariance => non-isomorphic under any perm (weight-8 count differs 1 vs 0).
