# Uniform local coverage and discarded tuples

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Use Y,x,h,J,B from local-sieves.md. All source parameters are formed from Y, not from the variable endpoints x and x+h. Write m=L_0(Y), the source's m, and G=G_m(Y). In this note X is not a second moving parameter. All limits take Y to infinity with H fixed, and then H to infinity.

## 1. A large-prime count once only the first simplex inequality is known

The early stage does not require the source's good prime bands. Outside the values with Omega(v)>5log_2 v, every preimage satisfies Omega(n)<=Omega(v)+1<=6B. The elementary inequality follows from the prime-power formula for phi: each odd prime contributes at least one prime factor to p-1, and only the prime2 can lose one factor. Also n<<YB.

Suppose the first Ford simplex inequality holds with coefficient xi_0<=1.001 and at least two coordinates retained. Since q_1>=q_2, it implies

    log_2 q_2 <= xi_0 B/(a_1+a_2) <0.9B.

Write n=q_0 q_1 r_2, where r_2 is the product of the prime factors after q_1. Then r_2<=exp(6B(log Y)^0.9)=Y^{o(1)}. Since n>=v>=Y/4 and q_0>=q_1, q_0^2>=q_0q_1=n/r_2>=Y^{1-o(1)}. Also q_1<=sqrt(n)<=sqrt(CYB), so n/q_0=q_1 r_2<=Y^{1/2+o(1)}. These calculations include q_0=q_1 without change. In particular q_0>=Y^{0.49} and n/q_0<=Y^{0.6} for large Y. We will only use the weaker bounds q_0>=Y^{1/3} and n/q_0<=Y^{0.7}.

Fix the remaining integer r=n/q_0, together with any further coordinate restrictions. Its totient is at most Y^{0.7}. Depending on whether q_0 divides r, the exact value is (q_0-1)phi(r) or q_0 phi(r). Dropping the divisibility restriction gives two prime intervals of length h/phi(r), centered at x/phi(r) or1+x/phi(r). Their endpoints are at least Y^{0.3}; their relative length is comparable to1/log Y. The quantitative PNT gives

    number of possible q_0 << h/(phi(r)log Y).     (9)

This handles repeated largest primes explicitly. It requires only the first simplex inequality and a controlled Omega count, not all the later inequalities or good-prefix bands. In applications we sum only r for which some feasible preimage exists, so the size bound for r is retained until (9) is applied.

## 2. Local Ford16 in the parameter range actually needed

Let0<=Psi<=sqrt(m), L=m-Psi an integer (integer rounding changes constants), and xi_i=1+10^-4 exp(-(m-i)/40). Then

    #{v in V intersect J: some preimage fails S_L(xi)
          or log_2 q_L<=2}
       << (hG/log Y) exp(-Psi^2/4),               (10)

up to an additional term o(hG/log Y) which is uniform throughout this Psi range and can be absorbed into the right side. The statement about q_L includes a missing prime. We justify both the local modification and the uniform error budget below.

For the first inequality failure, retain the same disjoint classification by the first failed index j as in Ford Section4 and the proof of Theorem16. Remove the high-Omega values at a global cost O(Y(log Y)^(-2.39)B), which is o((hG/log Y)exp(-m/4)). At j=0, use (8) with k=L and omega=10^-4 exp(-m/40). Since m~log B/log(1/rho),

    omega^2 B/(600 L^3 log L) >= B^c

for some fixed c>0 and all large Y, even after constant factors. Indeed1-1/(20log(1/rho))>0.9. Thus this part is o((hG/log Y)exp(-m/4)); W(CY)<<G absorbs the order scale.

For j>=1 the first inequality has passed. Hence (9) applies before any later band condition is imposed. Put w=q_j q_{j+1}..., d=phi(w). The strict break q_{j-1}>q_j makes this suffix coprime to the retained prefix. For j>=2 it follows from the preceding passed inequality, the failed one, increasing a_r and xi_{j-1}<=xi_j. For j=1, failure of the next inequality together with the first gives (a_1+xi_1)log_2 q_1<xi_0 B, so log_2 q_1<0.73B for large Y; the bound on Omega(n) and n>=Y/4 then gives q_0>q_1. This supplies the first-index boundary case explicitly. The source of the numerical small factor in Ford(4.8) is the reciprocal sum over these suffix totients and the truncated-prefix volume, not a count of the largest prime. Explicitly the argument preceding(4.8) bounds

    R_{j-1}(S_{j-1}(xi);Y) * sum_{eligible d}1/d
       << G exp[-(m-j)^2/4-c_0(m-j)]              (11)

with a positive constant c_0 (the displayed coefficient in Ford(4.8)). The small-d bound uses W(Y_j) and the large-d bound uses Ford4.2 globally for the suffix; neither is localized here or needs to be. This is also the bound invoked in the actual proof of Ford16 for the truncated list L=m-Psi. All the suffix and reciprocal-prefix estimates are unchanged. The only interval-sensitive operation was the count of q_0. Replace it by (9), with the same reciprocal weights. Consequently the local j-th first-failure contribution is at most h/log Y times the left side of (11). Summing over j<L, so m-j>Psi, gives the right side of (10). This is a factorized counting argument; it does not assert that an arbitrary subset of the global first-failure set is uniformly distributed.

For the terminal small/missing prime, retain Ford16's second argument inside the simplex. Use S=exp(B^100). Equation(5) removes non-S-nice values with relative error O(B^(6-100/6))=O(B^(-32/3)) compared with hG/log Y. This is smaller than exp(-m/4), since m~log B/log(1/rho). The first simplex inequality still supplies (9). Classify by k>Psi, where n has exactly m-k+1 primes larger than exp(exp2). The remaining small-prime factor contributes its same finite reciprocal Euler product. Ford's displayed reciprocal bound is

    R_{m-k}(xi^k;Y) << G exp(-k^2/(4C)),

where C=1/(2log(1/rho))<1. Counting q_0 with (9) and summing k>Psi gives O((hG/log Y)exp(-Psi^2/4)). No good-band condition has been used to manufacture a large prime; it came from the first simplex inequality and Omega cutoff.

The only auxiliary errors just discussed are exponentially small in B or O(B^(-32/3)). Since exp(-Psi^2/4)>=exp(-m/4)=B^{-1/(4log(1/rho))+o(1)}, they are uniformly absorbable. We do not claim a local Ford16 for arbitrary Psi close to m; that stronger auxiliary statement is unnecessary for T024W52.

## 3. Local normal coordinate bands

For a fixed0<eta<=0.04 and an integer P>=1 fixed before Y, the local analogue of the source's ford-bands estimate is

    #{v in V intersect J: some preimage has
         |log_2 q_i/b_i-1|>eta for some1<=i<=m-P}
       <<_eta (hG/log Y) exp(-c_eta P)
          +o_{Y;P}(hG/log Y).                   (12)

Here b_i=B rho^i(1-i/m), exactly the source b_i.

To verify the use of Ford10 rather than assume its localization, follow its actual proof through Lemma6.2. For small indices i<=3eta m, Lemma6.2(b)/(c) uses Psi=ceil(sqrt(2|theta|m)), with |theta|<=eta, so Psi<=sqrt m for large Y. For i>3eta m, the(a)/(d) choice is Psi=ceil(|theta|sqrt(m(m-i)/(2i))), also <=sqrt m. Thus (10) supplies its initial simplex exception estimate in every case used here.

The rest of Lemma6.2 counts preimages inside that simplex with one coordinate on the wrong side. Its equation(6.16) is obtained by counting q_0 and summing over the reciprocal small-tail totients and over the terminal-coordinate bins b. Replace only q_0's count by(9). The regions in (6.17)-(6.20), their thickening, the exponential terminal factor and the geometric Lemma6.1 are unchanged: all are independent of the interval for v. Thus the same numerical bounds hold with V(Y) replaced by a constant times hG/log Y, with the uniformly negligible errors from(10). The proof of Ford10 then gives, for the fixed eta,

    i<=3eta m:  C(hG/log Y) exp(-eta m/13),
    i>3eta m:  C_eta(hG/log Y) exp(-eta^2(m-i)/4).

Summing i<=m-P proves (12). The at-most-m uniformly negligible auxiliary terms remain negligible because the error budget in(10) has a large power-of-B margin. No phase regularity or changing endpoint parameter is used.

## 4. Coverage: every preimage, not only a selected good one

Use the source's H, P=floor(log log H), L=m-P and R=m-H. Apply(10) at Psi=P and(12) with eta=0.04, increasing Y for fixed H so that alpha/alpha_theta is sufficiently close to1. Outside their local exceptional union, EVERY preimage has the source simplex condition and coarse bands. The union quantifier comes from Ford's counts of values with some violating preimage, maintained in (5),(8),(10),(12).

The high-Omega exception above is negligible. For v in J there is no lower-value v<=Y^0.95 exception once Y is large. The p_1 band and Omega(n)<=6B now imply p_0>=Y^0.9 for all preimages, exactly as in the source. It remains to exclude an excessively large smooth tail a.

Fix p_1,...,p_L,a in such a failing preimage and let r=p_1...p_L a. The largest prime is distinct from every factor of r, so the exact value is(p_0-1)phi(r). If the interval is nonempty with p_0>=Y^0.9, then phi(r)<=C Y^0.1. The PNT upper bound in that interval is at most C h/(phi(r)log Y). Supermultiplicativity gives

    1/phi(r) <= [1/phi(a)] product_{i=1}^L1/(p_i-1).

Apply the unchanged source prime-box estimate and smooth-tail reciprocal estimate. This yields a local failing-tail bound at most

    C(hG/log Y) K_H exp[-exp(cP rho^(-P))].

Thus there is E_J, counting values with at least one nonbasic preimage, such that

    |E_J| <= (epsilon_H+o_{Y;H}(1)) hG/log Y,
    epsilon_H ->0.                              (13)

This bound includes both values having some basic and some nonbasic preimages and values having only nonbasic preimages. It does not dismiss the latter class or use a good witness to bound it. Outside E_J, all preimages are basic; in particular at least one exists and gives a source tuple.

## 5. Discarded tuples

Retain exactly the source's definition: a tuple is discarded if at least one of its basic witnesses fails one of the four good conditions at some i<=R. Count failing full witnesses as an upper bound. We prove

    |D_J| <= (epsilon'_H+o_{Y;H}(1)) hG/log Y,
    epsilon'_H ->0.                             (14)

Every basic witness already has its small cofactor bound. For any restriction independent of p_0, sum p_0 in the actual value interval. Its endpoint is Y^{1-o(1)} uniformly and the count is bounded by C h/log Y times the reciprocal cofactor. All source reciprocal estimates therefore retain their constants with h in place of Y.

This immediately handles the thin-slack condition (u_0=B is fixed, not log_2 p_0), all residual Omega(D_i) conditions, and all normality/square conditions at i>=1. It also handles i=0 normality failures involving p_j with j>=1. Their source bounds are the same convergent H-tails, respectively K_H H^-2 and the much faster normal/square/Omega tails displayed in extraction.tex.

Two cases involve p_0 itself. For its S_0-normality, S_0=exp(exp(B^(1/3))) lies between exp(B^36) and Y for all sufficiently large Y. Apply (2) at its interval endpoint z=Y^{1-o(1)} and length comparable to z/log Y. Relative to prime counting the saving is O(B^5 exp(-B^(1/3)/6)), which absorbs the source's exp(O(m^2)) reciprocal overcounts. It is o_{Y;H}(1).

For square failures in the i=0 block, use the actual global source square bound only for this subfamily. It is at most

    C(YG/log Y) K_H exp[Cm^2+CB-exp(c B/m^20)].

Replacing Y by h costs at most C log Y=exp(B+O(1)). The last negative term dominates both CB and this extra B because B/m^20 grows faster than log B. Hence this entire subfamily is o_{Y;H}(hG/log Y). This explicit strong saving avoids a false interval estimate for square divisibility with a missing endpoint remainder.

These cases exhaust the source's four good conditions, including those involving the first prime. They prove(14) with epsilon'_H tending to zero. The proof does not bound only the number of discarded values: it bounds discarded tuples with witness overcounting, as required by the source finite-map lemma.
