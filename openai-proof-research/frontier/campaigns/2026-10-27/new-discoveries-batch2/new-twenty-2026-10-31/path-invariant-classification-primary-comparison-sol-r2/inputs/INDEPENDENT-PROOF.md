# Independent full ordinary proof: 339209

Reviewer: GPT-6.1 Sol, high/default, personally; no children, formal tools, mathematical programs, enumeration, or experiments. This is an ordinary mathematical review, not acceptance or credit.

## Precise endpoint
For positive integers n,d put V=R^d. A real linear subspace W of V^n has f(W) contained in W for every f_i(x)=g(x_i)+sum_{j adjacent i}h(x_j-x_i), with g:V->V odd and h:V->V real-linear, if and only if W is the image of one of the following independent-vector words: choose a basic word S of length b dividing n and concatenate n/b blocks S,rev(S),S,rev(S),... . The basics are G_q=(a_1,...,a_q), q>=1; E_(2q-1)=(a_1,...,a_q,a_(q-1),...,a_1), q>=2; O_(2q)=(a_1,...,a_q,-a_q,...,-a_1), q>=1; O_(2q+1)=(a_1,...,a_q,0,-a_q,...,-a_1), q>=1; and O_1=(0). Each a_j ranges freely over V. Independence means freedom of parameters, not that each substituted tuple consists of linearly independent vectors in V.

The source's invariant predicate is pointwise f(W) subset W, Definition 2.2 p3. No existence/uniqueness theorem for nonsmooth flows is needed. The argument also works if admissible g is restricted to smooth odd functions, since its necessity tests are polynomial and its sufficiency uses only oddness. It does not classify arbitrary invariant subspaces for one fixed g,h.

## 1. Cell coordinates and cubic reduction
For a scalar vector u in R^n and standard coordinate vector v_a in R^d, write u[v_a] for its placement in that coordinate at all cells. All simultaneous endomorphisms I_n tensor A preserve W by taking g=A,h=0. Define U={u:u[v_1] in W}. Given x in W, apply matrix unit E_(1a); its result is x's a-th scalar cell-coordinate vector placed in coordinate1, so that scalar vector belongs to U. Conversely, for u in U, E_(a1) puts u in coordinate a inside W. Linearity then proves W consists exactly of tuples whose every scalar cell-coordinate vector belongs to the same U. This is the precise meaning of U tensor R^d, with no tensor-product theorem assumed.

Choose m=dim U coordinate functionals whose restrictions to U form a basis of its dual. Such a subset exists because all n coordinate functionals span the dual: their common kernel on U is zero. Projection on these selected coordinates is an isomorphism U->R^m. Write the other coordinates as linear forms c.y in the m free coordinates. The simultaneous coordinatewise cube g(v)=(v_1^3,...,v_d^3),h=0 preserves W. Applying it to u[v_1] shows scalar cubing preserves U. Thus for each row c,
(c.y)^3=sum_a c_a y_a^3 for all y in R^m.
Comparison of polynomial coefficients gives c_a^3=c_a and 3c_a^2 c_b=0 for a!=b. Consequently every row is zero or one signed standard unit. The selected free rows are standard units; the resulting n-by-m matrix R has full column rank and U=im R. This includes m=0, when U=0. Conversely, zero and signed-unit row maps commute with every odd vector g: g(0)=0, g(-v)=-g(v). This is why a scalar normal form suffices for arbitrary d, including d=1.

## 2. Quotient recurrence
Use the source's L=D-A, so (Lx)_i=sum_{j adjacent i}(x_i-x_j); the coupling with h=identity is -L. Since W is linear, invariance under -L and L are equivalent. By the preceding coordinate identification this is equivalent to L U subset U. Since R:R^m->U is an isomorphism, this holds iff there is a unique m-by-m matrix Q with LR=RQ. Here r_i is the i-th ROW of R, acting on column parameters. Conversely, LR=RQ implies the coupling for any linear h sends Ry to Rz with z_a=-sum_b Q_ab h(y_b). Together with the odd-g contribution z_a=g(y_a), this proves universal invariance. This formula fixes the sign and orientation of the arbitrary-linear-h bridge.

Put r_0=r_1 and r_(n+1)=r_n. The path degree1 endpoints and degree2 interior give, for every real vertex i,
r_(i+1)=2r_i-r_(i-1)-r_i Q.                    (*)
For n=1 the same equation gives r_1 Q=0, correctly L=0. If r_1=0, the equation at1 forces r_2=0 (virtual if n=1), then induction forces every real row zero. Hence m=0 and O1 gives W=0. Assume henceforth r_1 nonzero and rename/orient its parameter as e_1.

## 3. First return, without assuming all parameters have occurred
Until a row is zero or returns to a previously seen unsigned class, orient each new class positively and name it in order. If all n rows are new, R is the identity after this change of parameters, W=V^n, given by G_n. Otherwise there is q<n with r_i=e_i for 1<=i<=q and t=r_(q+1) either zero or +/-e_j, j<=q. There might still be m-q unseen coordinates: do not discard them yet.

When q>=2 the known equations determine
 e_1 Q=e_1-e_2,
 e_i Q=2e_i-e_(i-1)-e_(i+1) (2<=i<q),
 e_q Q=2e_q-e_(q-1)-t.
In particular S=span(e_1,...,e_q) is Q-invariant even if m>q. Starting from r_q,t in S, recurrence (*) puts every later row in S. Full column rank of R now forces m=q: an unseen class cannot appear later. This pays the delayed-class bridge before relying on Q being fully specified.

If q>=2 and t=e_j with 2<=j<q, the next row is e_(j-1)+e_(j+1)-e_q. If j<q-1 its three indices are distinct, so it is outside the row alphabet {0,+/-e_a}. If j=q-1 it is e_(q-2), allowed for q>=3. For j=1 the next row is e_1+e_2-e_q: forbidden for q>2, but equal to e_1 for q=2. The latter is the same t=e_(q-1) case, not an extra family.

If t=-e_j with 2<=j<q, the next row is -e_(j-1)-e_(j+1)-e_q. Distinct indices give three negative units; if j=q-1 the merging index q has coefficient -2. Both are forbidden. For t=-e_1 the next row is -e_1-e_2-e_q; q=2 merges to -e_1-2e_2, still forbidden. The unexcluded cases are precisely
 A: t=e_q; B: t=e_(q-1); C: t=-e_q; D: t=0.
These arguments remain valid when q+1=n: the next row is r_(n+1)=t, a virtual row that is still in the alphabet. It cannot equal any of the displayed forbidden vectors. No equation at a virtual vertex is being invoked: (*) is applied at the last REAL vertex.

For q=1, t is e_1,-e_1, or0. The endpoint equation is e_1 Q=e_1-t, not the q>=2 formula. Q preserves span e_1, recurrence excludes delayed parameters, and these are A,C,D. There is no B with q=1.

## 4. Global templates and local verification
For q>=2 define Q on the basis by the preceding left/interior rules and the following last row:
 A: e_q Q=e_q-e_(q-1), b=q, S=G_q;
 B: e_q Q=2e_q-2e_(q-1), b=2q-1, S=E_(2q-1);
 C: e_q Q=3e_q-e_(q-1), b=2q, S=O_(2q);
 D: e_q Q=2e_q-e_(q-1), b=2q+1, S=O_(2q+1).
Extend S to the infinite sequence S,rev(S),S,rev(S),... and put r_0=r_1. We check (*) in the equivalent neighbor-sum form r_(i-1)+r_(i+1)=2r_i-r_i Q.

Every interior occurrence of +/-e_j, 1<j<q, has neighbors +/-e_(j-1), +/-e_(j+1), with the same sign, and satisfies the interior row formula. Reversing a word swaps the two neighbors and does not affect their sum; changing all signs preserves the equation. Thus it suffices to list the exceptional triples at turns:
 A: neighbors of e_q are (e_(q-1),e_q), sum e_(q-1)+e_q;
 B: neighbors of e_q are (e_(q-1),e_(q-1)), sum2e_(q-1);
 C: neighbors of e_q are (e_(q-1),-e_q), sum e_(q-1)-e_q;
 D: neighbors of e_q are (e_(q-1),0), sum e_(q-1), and neighbors of0 are (e_q,-e_q), sum0.
Each sum is exactly 2e_q-e_q Q (or zero for the zero row), and negative/reversed turns follow by the two identities just stated. At every block junction the doubled outer letter is +/-e_1. Its neighbors are that same signed e_1 and signed e_2, whose sum equals +/-(2e_1-e_1 Q). This also verifies the artificial left row r_0=r_1. For q=2 the interior range is empty; the left and last-row rules apply to different basis vectors and the triples above are still valid. In B,q=2 the whole word is e_1,e_2,e_1; its only special center has sum2e_1, as required.

For q=1 use instead Q=0 in A, Q=2 in C, Q=1 in D, as scalars on e_1. In A all rows e_1 have neighbor sum2e_1. In C the infinite word is e_1,-e_1,-e_1,e_1,e_1,-e_1,...; each signed nonzero row has one equal neighbor and one opposite neighbor, sum0=(2-Q)r_i. In D it is e_1,0,-e_1,-e_1,0,e_1,e_1,...; a nonzero row has neighbors itself and0, sum r_i=(2-Q)r_i, while0 has opposite neighbors. These statements also apply at the left endpoint by the chosen r_0.

Hence every infinite template satisfies the recurrence at every positive index, not just at sample orders. Its first q+1 rows agree with the original. With fixed Q, (*) uniquely determines the next row from the preceding two, so induction identifies the entire original finite word with the appropriate template. No spectral assumption or finite evidence is used.

## 5. Exact stopping positions
For A,q>=2 every adjacent pair INSIDE a basic block consists of distinct basis indices. For B,q>=2 adjacent internal indices differ even across the single peak; the peak is not doubled. For C adjacent internal entries either have different indices or are e_q,-e_q, which differ over R. For D the two internal zero transitions have one zero and one nonzero row, and all other internal pairs have distinct indices; zero is isolated. Reversal preserves inequality of neighbors. At every block junction the final entry of a block equals the first of its reversal, so these, and only these, are equal consecutive rows. Thus r_i=r_(i+1) iff i is a positive multiple of b. The explicit q=1 A,C,D words have the same property with b=1,2,3 respectively. The all-zero case O1 has b=1 and equality everywhere.

The right boundary therefore holds iff b divides n. This remains valid when the first return occurs at the last real row: the original recurrence fixes its next virtual row, and equality is tested there. The whole-space no-return case is already G_n with b=n. For n=1 the possibilities are precisely0 and V, from O1 and G1. For n=0 the source connected nonempty graph convention does not supply a path algorithm with positive factorization; if P0 is defined separately its phase space is the singleton zero-dimensional space, with one invariant subspace, handled separately rather than claiming a factorization of0 into positive b,k. Likewise d=0, outside the requested positive cell dimension, collapses every word to that same subspace.

## 6. Converse
For each positive b,k and each listed basic word of length b, the above local check supplies a Q and both boundary equalities at n=bk, so LR=RQ. Each nonzero independent parameter appears, so the row map has full column rank; O1 is treated as m=0. For x_i=sum_a r_ia y_a, oddness gives g(x_i)=sum_a r_ia g(y_a), and linearity gives the coupling as -sum_a r_ia sum_b Q_ab h(y_b). Thus f(x)=Rz belongs to the word image for every odd vector g and every linear endomorphism h. This proves both directions of the literal source algorithm for all positive n,d.

## Verdict on the author's proof
No mathematical gap found in the FULL equivalence. The candidate's short delayed-class explanation is valid, but the span-invariance argument in section3 above makes its quantifier explicit. The matrix-unit proof and the complete local-neighbor check above fill exposition, not a narrower replacement theorem. This ordinary PASS is not novelty clearance, formal certification, self-acceptance, or a campaign count.
