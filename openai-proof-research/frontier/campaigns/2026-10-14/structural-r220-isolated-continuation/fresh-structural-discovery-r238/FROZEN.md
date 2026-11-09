# Structural238: frozen statement and author-proof scope

Frozen after complete operative reading of both Source363 papers, the primary comparison in COMPARISON.md, the prospective guarded history pass, and the feasibility calculations in PREFREEZE.md. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and its operative proofs are stipulated true. No correctness, contribution, acceptance or count is assigned here.

## Exact statement

Let Omega=T³_x × R³_v, with T³=R³/Z³ of volume one, ordinary sphere surface area d omega, a=(v-v_*)·omega, v'=v-a omega and v_*'=v_*+a omega. At a common (t,x), set

  Q^+(F,F)(v)=integral |a|F(v')F(v_*') dv_* d omega,
  Q^-(F,F)(v)=integral |a|F(v)F(v_*) dv_* d omega,
  Q=Q^+-Q^-.

Let M(v)=(2 pi)^(-3/2) exp(-|v|²/2) and eta_M(z,v)=z log(z/M(v))-z+M(v), with 0 log 0=0. Let Phi(A,B)=(A-B)log(A/B) for A,B>0, Phi(0,0)=0, and Phi(A,0)=Phi(0,A)=+infinity for A>0.

There exist R<infinity, one measurable F_0>=0 with F_0(x,v)=0 for |v|>R and integral F_0(1+|v|²+|log F_0|)<infinity, and two global functions F^(1),F^(2)>=0 with the following properties.

1. Each is a global entropy solution with local conservation in the precise sense of Definition 1.1 (label def:admissible) of the October 5 Source363 paper, for this same F_0 and this exact kernel, angular measure and velocity domain. In particular the renormalized equations, initial trace, entropy inequality, and exact local balances for 1,v_1,v_2,v_3,|v|²/2 all hold with their prescribed initial traces.
2. For every real k>=0 and every finite T, F^(i) belongs to C([0,T];L1(Omega,<v>^k dx dv)) and integral_0^T integral_Omega <v>^k[Q^+(F^(i),F^(i))+Q^-(F^(i),F^(i))]<infinity. The two solutions differ on a set of positive (t,x,v) measure.
3. For each i, k>=0 and finite T, the function eta_M(F^(i)(t),v) belongs to C([0,T];L1(Omega,<v>^k dx dv)). In particular this continuity includes t=0 with value eta_M(F_0,v).
4. For each i and finite T,

   integral_0^T integral_Omega (Q^++Q^-)|log F^(i)| < infinity.

   At F^(i)=0 the product in this assertion is assigned zero; the proof must establish that Q^++Q^-=0 almost everywhere on that zero set.
5. Define the nonnegative entropy density and dissipation density, and the entropy flux, by

   s_i(t,x)=integral eta_M(F^(i)(t,x,v),v) dv,
   J_i(t,x)=integral v eta_M(F^(i)(t,x,v),v) dv,
   d_i(t,x)=(1/4)integral |a| Phi(F^(i)' F^(i)_*',F^(i)F^(i)_*) dv dv_* d omega.

   On each finite interval, d_i is integrable, and s_i,J_i are continuous into L1(T³). Exact local entropy balance, including the initial entropy trace, holds: for every phi in C_c^infinity([0,infinity)×T³),

   integral_0^infinity integral_T³ [s_i partial_t phi + J_i·grad_x phi - d_i phi]
       + integral_T³ s_0 phi(0,x) = 0,

   where s_0=integral eta_M(F_0,v)dv. Consequently, for EVERY 0<=a<=b<infinity,

   H_M(F^(i)(b)) + integral_a^b integral_T³ d_i = H_M(F^(i)(a)).

No positive lower bound, persistent compact velocity support, additional branches, continuity in a construction parameter, uniqueness, convergence of approximate dissipations, or statement about every entropy solution with datum F_0 is asserted.

## Frozen proof scope

Use the unchanged October dormant/cap pair after its full global colored continuation and separation. Derive from the deterministic cold and hot envelopes: a pointwise logarithmic upper bound, polynomially weighted logarithmic axial moments, logarithmically summable collision-envelope squares, and uniform every-time entropy tails. Prove the outgoing-sphere logarithm estimate with the exact hard-sphere normalization. Establish positive gain/loss logarithms, negative loss logarithms, and the negative gain logarithm via finite source dissipation and collision symmetries, treating vacuum explicitly. Prove weighted entropy continuity by uniform integrability and the source every-time strong trace. Apply the regularized characteristic chain rule, remove cutoffs, symmetrize the absolutely integrable collision logarithms, and prove the exact local identity and all-endpoint equality. Preserve all source properties and its final positive-measure separation without modifying either solution. Compare the completed operation with the actual primary proofs already read. No narrowing or renaming of this statement or proof scope is permitted to obtain a verdict.
