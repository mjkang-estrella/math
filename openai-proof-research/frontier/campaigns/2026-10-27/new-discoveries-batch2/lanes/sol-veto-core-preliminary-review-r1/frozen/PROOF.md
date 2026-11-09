# Proposed ordinary resolution of Rossi's rank-score distortion conjecture

Status: complete ordinary argument proposed by this lane; NOT independently reviewed,
accepted, formally certified, or cleared against all prior literature. No count requested.

## Statement and dependencies

Let n>=1 voters strictly rank m>=2 candidates, with ties in distance resolved
arbitrarily. Let s=(1,s2,...,sm) be nonnegative and nonincreasing, put S=sum(s),
v=sm, T=S-v, and q(c)=score(c)/(nS). For every consistent pseudometric and
every candidate a in the uniform-voter q-veto core,

    SC(a) <= (1+2T) SC(b)                         (A)

for EVERY candidate b. In particular take b optimal. Together with Rossi's
already-public Lemma 5 this gives exact worst-case distortion 1+2T for rational
s, including all finite profiles and every core member. The proof of the upper
bound works for real s as well. For m=1 the only candidate has distortion 1.

External combinatorial dependency: Rossi 2610.26535v1, Lemma 1 and Proposition 3:
core membership provides a fractional matching W(i,c), row sums 1/n, column
sums q(c), supported on a weakly preferred to c by i. This is the classical
weighted Hall/flow bridge, explicitly credited, not a new result. Metric and
scalar steps below are proved here. Berger et al. 2307.07495v3, Section 3.1,
is the closest proof: we refine its plurality-token decomposition by preserving
the complete column of b and its intersection with voters whose favorite is b.

## 1. Split the matching, keeping the b column

Fix b; if a=b there is nothing to prove. Write f(i) for i's first-ranked
candidate, F={i:f(i)=b}, p=|F|/n, mu=1/S, q=q(b). Each c has
q(c)>=mu*|{i:f(i)=c}|/n. Also the score floor gives

    q >= [p+v(1-p)]/S.                          (1)

For each c != b, split its incoming matching mass into good arcs to each
voter j with f(j)=c, of mass

    G(i,j)= W(i,c)*mu/(n*q(c)),

and residual mass. If q(c)=0 there are no such voters or positive incoming
arcs, so this column contributes nothing. Keep ALL W(i,b) as special arcs
to b. All residual arcs are bad. This is a nonnegative splitting: the total
good proportion of column c is mu*|{j:f(j)=c}|/(n*q(c))<=1.

For every j not in F, the good incoming mass is exactly mu/n. There are no
good arcs to F. Total good mass is mu(1-p), total special mass q, and total
bad mass is 1-K, where

    K=mu(1-p)+q <= 1.                          (2)

The row sums across all three pieces remain 1/n.

## 2. Metric inequalities with the first-choice cost retained

Put r_i=d(i,b), x_i=d(i,a), D=d(a,b),
R=(1/n)sum_i r_i, H=(1/n)sum_{i in F} r_i,
and E=(1/n)sum_i(x_i-r_i). All are finite; R,H,D>=0.

On a good arc (i,j), consistency gives x_i<=d(i,f(j)), and
d(j,f(j))<=r_j. Consequently

    x_i <= r_i+d(b,f(j)) <= r_i+2r_j,
    D <= x_i+r_i <= 2(r_i+r_j).              (3)

On a special arc (i,b), x_i<=r_i, so E's local excess is <=0 and
D<=2r_i. On every bad arc x_i-r_i<=D by the triangle inequality.
Summing over the splitting, using its exact good column sums, proves

    E <= 2mu(R-H)+(1-K)D,                    (4)
    (1+mu)R-mu H >= KD/2.                   (5)

For (5), summing r_i over good and special arcs is at most R, and summing
r_j on good arcs is mu(R-H). This is the needed fractional coupling dual.

At most 1-p of the total special mass can originate outside F (their total
row capacity). Thus special mass at least q+p-1 originates inside F.
Its source voters satisfy r_i>=D/2, hence

    H >= (D/2) max(0,q+p-1).                 (6)

This intersection bound is essential; discarding it recreates the gap.

## 3. The universal scalar certificate

Since m>=2, T>=1, S>=1, 0<=v<=1 and 0<mu<=1, so T-mu>=0.
We claim

    (T+1)[K+mu max(0,q+p-1)] >= 1+mu.       (7)

If p<=T/(T+1), (1) implies

    (T+1)K-(1+mu)
      >= v[T-(T+1)p]/S >=0.

If p>=T/(T+1), (1), S=T+v and v<=1 imply

    q-1/(T+1)
      >= (1-v)[(T+1)p-T]/[S(T+1)] >=0.

Then q+p>=1 and direct expansion gives

    K+mu(q+p-1)=(1+mu)q.

This proves (7) in the second case too. There are no restrictions on m or n.

If D=0, every x_i=r_i and (A) follows. Otherwise use (5), with
T-mu>=0, to obtain

    2(T-mu)R+2mu H-(1-K)D
      >= {[(T+1)K-(1+mu)]D+2mu(T+1)H}/(1+mu)
      >= 0,                                  (8)

where the last inequality uses (6) and (7). Combining (4) and (8) gives
E<=2T R, exactly (A). This does not divide by SC(b); if it is zero the
same inequality forces SC(a)=0. Positive-cost ratios have the stated bound.

## 4. Sharpness (public source construction, not new credit)

Place m-1 candidates, including a=b1, at -1, and b at +1. Put n1 voters
at 0 ranking b1,...,b_(m-1),b; put n2 voters at +1 ranking
b,b1,...,b_(m-1). Choose n2/n1=T, possible for rational s. The +1 voters
are adjacent to all negative candidates in a's domination graph, whose total
q-weight is [n1*T+n2*(S-1)]/[(n1+n2)S]. Their row mass n2/(n1+n2)
is exactly this quantity. They can fill all negative columns; the 0 voters,
adjacent to every candidate, fill b. This explicitly provides the matching.
The costs are SC(b)=n1 and SC(a)=n1+2n2, so the ratio is 1+2T.
b is optimal because T>=1 and all other candidates have the latter cost.
This is Rossi Lemma 5 verbatim in mathematical content, credited to that source.

## Scope, source fidelity and priority limits

The literal conjecture is unnumbered after Lemma 5 on printed p9 of Rossi,
arXiv2610.26535v1 (19 October 2026). Definitions 1/2 require rational scores;
Section 2 permits pseudometrics and arbitrary distance ties. No electorate,
candidate-count, line-metric, unique-winner or positive-last-score restriction
has entered the upper proof. The symbolic m=3 specialization is S=1+u+v,
T=1+u and the split point p=(1+u)/(2+u), for every 0<=v<=u<=1.

The ordinary proof is proposed, not an independent clearance decision. Its
ingredients include classical weighted Hall and the known plurality coupling.
Neither shortness nor those ingredients alone establishes prior subsumption.
The new step relative to the body-read Berger proof is (6) together with the
first-choice cost H retained in (4)/(5). This comparison is bounded, and a
specialist prior-art review could still find an earlier complete bridge.
