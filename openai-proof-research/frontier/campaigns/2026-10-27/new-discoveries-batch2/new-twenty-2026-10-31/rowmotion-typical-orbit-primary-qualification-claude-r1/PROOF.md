# PROOF.md — independent reconstruction for MathDB 368315

Written BEFORE inputs/author-candidate.md was opened. The route (rotation of 2m marks on a
cycle of length m+n+1, fixed noncrossing matching, hidden zone of m-1 positions) was disclosed
by the task; the argument and every computation below are mine. No program or enumeration was
used; small cases were checked by hand.

Claim. For every fixed m>=1 the fraction r(n) of IC([m]x[n]) in rowmotion orbits of size exactly
N:=m+n+1 satisfies r(n)=1-O_m(1/n). In particular r(n)->1.

Notation. P=[m]x[n], rows i=1..m, columns j=1..n, (i,j)<=(k,l) iff i<=k and j<=l.
Only source input: Theorem 1.1 of arXiv 2505.04000v1, glyphs viewed on p.4:
  Row(I) = ( Inc(Ceil I) - I ) U ( DCeil I - D(Min I n DCeil I) ).
(D = order ideal generated; Inc(emptyset)=P.)

## 1. Full interval-closed sets

Call I FULL if every row meets I. Then row i of I is an interval [a_i,b_i].

L1. For full I: a_1>=...>=a_m and b_1>=...>=b_m; conversely any such data with a_i<=b_i is an ICS.
Proof. Rows i,i+1. If b_{i+1}>=a_i, then (i,a_i)<=(i+1,b_{i+1}), so convexity puts (i+1,a_i) and
(i,b_{i+1}) in I, giving a_{i+1}<=a_i and b_{i+1}<=b_i. If b_{i+1}<a_i, then a_{i+1}<=b_{i+1}<a_i<=b_i.
Converse: for x in row i, y in row k>i, x<=y gives a_k<=a_i<=x<=y<=b_k<=b_i, so everything between is in I.

Let R={i: b_i<n and (i=1 or b_i<b_{i-1})}, S={i: i=1 or a_i<a_{i-1}}.
For k: k*:=min{i in R: i>=k}, u_k:=b_{k*}+1 (u_k:=0 if none).

L2. For full I: L(I):=D(I)-I has row k equal to columns <a_k; Ceil I={(i,b_i+1): i in R}; Min I={(i,a_i): i in S}=Min(P-L(I));
Ceil I=Min(P-D(I)); row k of DCeil I is columns <=u_k.
Proof. Direct from L1. For Ceil: if b_i=b_{i-1} then (i-1,b_i+1) lies in the filter minus I strictly below (i,b_i+1). Conversely if z=(i',j')<(i,b_i+1) were in the filter minus I, then j'>b_{i'}>=b_i and j'<=b_i+1 force b_{i'}=b_i, impossible for i'<i when i in R.

L3 (new row formula). For full I, row k of Row(I) is the integer interval
   ( w_k , max(u_k, a_k-1) ],   w_k:=max({0} U {a_i: i>=k, i in S, a_i<=u_i}).
Proof. Row k of Inc(Ceil I) is the open interval (u_k,v_k), v_k:=min{b_i+1: i in R, i<=k} (+infinity if none). If k in R then v_k=u_k=b_k+1, so this part is empty. If k not in R then, looking at the first index of the block of equal b's, either v_k=b_k+1 or (v_k=infinity and b_k=n); removing [a_k,b_k] leaves (u_k,a_k). Row k of the second term is (w_k,u_k]. Since a_i<=u_i<=u_k for eligible i, w_k<=u_k. Thus: if k in R, row k is (w_k,u_k], and u_k=b_k+1>=a_k-1. If k not in R and a_k<=u_k, row k is (w_k,u_k]. If k not in R and a_k>u_k, row k is (w_k,u_k] U (u_k,a_k)=(w_k,a_k), and a_k-1>=u_k. []

With marks o_k:=a_k-1, c_k:=b_k+1, L3 reads
   c'_k = 1+max(c_{k*}, o_k)    (c_{k*}:=-infinity if no k*),
   o'_k = 1+max({-1} U {o_i: i>=k, i in S, o_i<c_{i*}}).        (*)

Hand cross-checks of L3 by literal toggling, row m down to 1, right to left: chain m=1 for all [a,b]; m=2 with b_1=n and a_1<=b_2 gives row 1 -> [a_1+1,b_2+1]; m=2 with b_1=n and a_1>b_2+2 gives row 1 -> [a_2+1,a_1-1]. All agree.

## 2. Enumeration

If all rows are nonempty and all 2m numbers a_i,b_i are distinct then L1 forces strict decrease and a_i<b_i, and conversely every strict pattern is an ICS. Such tuples number C_m*binom(n,2m) (fillings of a 2xm standard tableau). Every other ICS has an empty row (at most m(1+binom(n+1,2))^(m-1)=O(n^(2m-2))) or a coincidence among the 2m numbers (O(n^(2m-1))). Hence
   |IC(P)| = C_m binom(n,2m) + O_m(n^(2m-1)) = (1+O(1/n)) n^(2m)/(m!(m+1)!).
This is elementary and does not need the source's reference [12].

## 3. Route R: rotation of marks (complete, self-contained given Theorem 1.1)

Cycle Z_N, positions 0..n+m. Visible V={0,...,n+1}; hidden H={n+2,...,n+m} (m-1 positions). A diagram D=(X,mu): X a 2m-subset with all cyclic gaps >=m+1, mu a noncrossing perfect matching of X. rho(D)=D+1.
Since {n+1,...,n+m,0} is m+1 consecutive positions, at most one point of X lies in it.

Decoding Phi(D):
(V) X in V: linear order; each chord has an opener and a closer; openers o_1>...>o_m, closers c_1>...>c_m; row i is the open interval (o_i,c_i). Dyck implies o_i<c_i.
(H) X n H={h}, h=n+1+t, 1<=t<=m-1, with mate p in V. Other chords do not straddle p. Let kappa:=1+#(chords entirely right of p). With sorted (at the current time) remaining openers/closers, using the time-0 names (each shifted by t):
  if t<kappa: openers o_1>...>o_m with o_kappa=p; closer of row i is c_{i+1} for i<=t, and c_i for i>=t+1 (so rows t,t+1 share c_{t+1});
  if t>=kappa: closers c_2..c_kappa,p,c_{kappa+1}.. in order; opener of row i is o_i (i<kappa), o_{i+1} (kappa<=i<=t), o_i (i>=t+1) (so rows t,t+1 share o_{t+1}).
All rows are nonempty because gaps >=2.

Here time-0 names refer to the state with h at n+1: c_1=n+1, o_kappa=p, and kappa=min{j: o_j>c_{j+1}} (c_{m+1}:=-infinity); the Dyck structure gives o_j<c_{j+1} for j<kappa and c_{kappa+1}<p<c_kappa.

Theorem R. Row(Phi(D))=Phi(rho D) for every diagram D.
Proof, by (*); offsets of t suppressed.
T0 (X in V, c_1<=n): R=S=[m], k*=k, so c'_k=c_k+1, o'_k=o_k+1.
T1 (X in V, c_1=n+1): R={2..m}, S=[m], 1*=2. c'_1=1+max(c_2,o_1): equals p+1 if kappa=1, c_2+1 if kappa>=2. o'_1 is o_2+1 if kappa=1 (o_1 ineligible; 0 if m=1), o_1+1 otherwise. k>=2: shifts. This is the t=1 state.
T2 (t<kappa, t+1<=m-1 or arrival): only b_{t+1}=b_t fails strictness, so R=[m]-{t+1}, S=[m], (t+1)*=t+2. For k!=t+1 both marks shift. c'_{t+1}=1+max(c_{t+2},o_{t+1}), and o_{t+1} is eligible in (*) iff o_{t+1}<c_{t+2}. If o_{t+1}<c_{t+2} then kappa>t+1, c'_{t+1}=c_{t+2}+1, o'_{t+1}=o_{t+1}+1: the doubling moves to rows t+1,t+2. If o_{t+1}>c_{t+2} or t+1=m then kappa=t+1, c'_{t+1}=p+1, o'_{t+1}=o_{t+2}+1 (or 0 if t+1=m): the flip happens at time kappa.
T3 (t>=kappa): R=[m], S=[m]-{t+1}, so closers all shift; o'_k=o_k+1 for k!=t+1 and o'_{t+1}=o_{t+2}+1 (or 0 if t+1=m).
At time m the hidden mark arrives at position 0 as the new smallest opener, its mate p+m is a closer, and the row pattern is exactly the sorted reading (c_{kappa+1}<p<c_kappa), i.e. case (V). m=1 is T1 with arrival at once. []

Corollary. If I=Phi(D) with X in V, then Row^t(I)=Phi(rho^t D), Row^N(I)=I. If Row^t(I)=I with 0<t<N, then rho^t D has no hidden mark (a hidden state has two rows sharing a mark while I has all 2m numbers distinct), so X+t=X, reading marks off. Therefore the orbit has size exactly N unless X is rotation-invariant.

Count. G_n:={I with all rows nonempty, strict, X subset V with all cyclic gaps>=m+1}: the complement in the strict patterns is O(n^(2m-1)) (a bounded difference between two of 2m parameters, or the one wrap-around condition). Rotation-invariant X: a nontrivial stabilizer of order e>=2 has e|2m, and X is determined by 2m/e<=m points of Z_N/(subgroup): at most 2m*C_m*N^m=O(n^m)=O(n^(2m-1)) ICS. Hence r(n)>=1-O_m(1/n). QED.

m=1 exact: N=n+2; [a,n]->[1,a-1]; orbit sizes n+2 except length n/2 (size (n+2)/2) and {emptyset,P} (size 2).

## 4. Route C: conjugacy with rowmotion on J(P x [2])  (NEW adversarial finding; external inputs to be read)

Write an order ideal of P x[2] as (A,B), B subset A, order ideals of P. Rowmotion on J(Px[2]) is
   Row_J(A,B) = ( D Min(P-A) U B', B' ),   B' = D( Min(P-B) n A ).
For full I put psi(I):=( DCeil I U L(I), L(I) ).

Theorem C. If I and J:=Row(I) are both full, then D(J)=DCeil I U L(I), L(J)=D(Min I n DCeil I), and psi(J)=Row_J(psi I). Moreover psi is injective on {I full with Row(I) full}.
Proof. L3 gives J=(row k) (w_k, max(u_k,a_k-1)], and the rows of L(J) and D(J) are the first two displayed sets. By L2, Min(P-L(I))=Min I, so Min(P-B) n A=Min I n DCeil I (Min I is disjoint from L(I)), so B'=L(J). By L2 for J, Min(P-D(J))=Ceil J, so the first component of Row_J(psi I), with A=D(J), is DCeil J U L(J). Injectivity: psi(I) determines B' and A=D(J), hence J=D(J)-L(J), hence I since Row is a bijection. []

No genericity assumption is used. Let E be the set of nonfull ICS, |E|=O(n^(2m-2)). The set of I with Row^t(I) in E for some 0<=t<=N+1 has size <=(N+2)|E|=O(n^(2m-1)), because Row is a bijection. For all other I, Theorem C gives psi(Row^N I)=Row_J^N psi(I). If Row_J has order dividing N=m+n+1 on J([m]x[n]x[2]) (Cameron-Fon-Der-Flaass, to be read), then Row^N(I)=I. So all but O(n^(2m-1)) ICS have orbit size dividing N, by a one-paragraph reduction to classical order-ideal rowmotion, with no mark analysis.
The remaining point for an orbit of size EXACTLY N is short orbits of Row_J; Route R settles it directly, and if the orbit structure of Row_J on J([2]x[m]x[n]) is known as rotation of noncrossing partitions of [N] (Pechenik; Dilks-Pechenik-Striker, to be read) then it also follows externally: ICS in short orbits inject under psi into elements of J in short orbits.
