# Frozen full target P3R

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Frozen after screening-before-freeze.md and before the sustained proof write-up. No narrowed substitute is authorized by this file.

For every a>0, every 0<rho<1/2, and every finite integer m>=3, let u_1^+,u_2^+,u_3^+ and u_1^-,u_2^-,u_3^- be any unit vectors in C^m with Gram matrices

    G+ = [[1,rho,rho],[rho,1,rho],[rho,rho,1]],
    G- = [[1,rho,-rho],[rho,1,rho],[-rho,rho,1]].

Put P_i^epsilon=u_i^epsilon(u_i^epsilon)*, w_a(x)=3a^2 sech^2(2ax), and for every R>=0 define the self-adjoint Schrödinger operator on L^2(R;C^m)

    H_epsilon(R) = -d^2/dx^2 - sum_(i=1)^3 w_a(x-(i-1)R) P_i^epsilon,
    S_epsilon(R) = Tr(H_epsilon(R))_-.

The target asserts all of the following as one package:

1. Each H_epsilon(R) has exactly three negative eigenvalues, counted with multiplicity, for every R>=0. Thus S is the **full** negative trace, with no omitted threshold eigenvalues.
2. Every one-well or two-well subsystem for the + triple is related to its - counterpart by one constant unitary, at every R. Hence all such subsystem spectra agree exactly.
3. S_+(R)-S_-(R) is continuous on [0,infinity), is strictly negative on some interval 0<=R<r_0(a,rho), and is strictly positive for all R>r_1(a,rho).
4. With A_a=sqrt(4a/pi), the normalized one-well bound-state tail coefficient, the exact asymptotic is

    lim_(R->infinity) exp(4aR) [S_+(R)-S_-(R)] / R^2
       = 64 a A_a^6 rho^3 = 4096 a^4 rho^3 / pi^3.

No uniqueness or location of a crossing, monotonicity in R, all-phase ordering, arbitrary well shape, unequal spacing/scale, endpoint rho=1/2, infinite matrix dimension, quantitative Lieb–Thirring stability, or full phase classification is claimed. All m>=3 and all triples with the stated Grams remain included. The two configurations can already be realized in R^3, and adding inactive channels does not change S.

Source family 262 is the sole pinned family. The target is a new deduction to prove, not a stipulated theorem. Source theorem truth at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is accepted only on its exact stated hypotheses. counted=false; no independent proof/contribution PASS is asserted.
