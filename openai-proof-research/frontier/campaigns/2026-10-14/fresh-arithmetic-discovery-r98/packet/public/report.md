# Arithmetic r98: public report

Status: PREFREEZE. No frozen target, no nominee. No mathematical gate, contribution gate or count is assigned by this round.

Runner: Factory Droid / claude-opus-5-5 / high. Pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Summary

Family 009 (compatible maps of mod-$p$ Milnor $K$-theory), continuing r97. As the r98 brief required, the actual lineation and place primaries were read before any further valuation-ring derivation. Carter–Vogt (PNAS 1980) is an announcement with no proofs. Machala (1975) is a complete, published proof of a higher-dimensional place theorem.

With Machala's theorem, r97's Proposition A, and the multiplicativity step from the pinned source's proof of `thm:main`, the $p=2$ classification closes on one stratum. That stratum consists of compatible maps under which every projective line keeps three distinct image points. Theorem D below proves this. Its proof composes a classical place theorem with the pinned proof's own gluing step. The brief names exactly this pattern as one that makes a full extension technical, so Theorem D is recorded as an author screen and not frozen as a nominee.

The unpaid part of the comparison gap is now located exactly. It is the classification on maps with a *collapsing line*, meaning a projective line with at most two image points. Lemma E and Example G show that this stratum already contains maps all of whose plane restrictions are reduced (triangle image). That stratum needs the reduced-lineation theory. Carter–Vogt announce that theory for planes only, and its proofs (Mem. AMS 235) were not obtained. Example F records that for odd $p$ compatible maps are not lineations at all, even bijective ones.

## Notation (as in the source and r97)

Source: `preprints/Reconstruction-from-Milnor-K-theory-modulo-the-characteristic-October-5-2026/build/build/`, labels `thm:main`, `lem:p-basis`, `lem:zero-symbol`, `lem:affine-symbol`, `prop:projective-lift`.

For a field $F$ of characteristic $p$, $V_F=F^\times/F^{\times p}$ (additive notation, $[1]=0$), $R_F\subset V_F\otimes V_F$ is spanned by $[f]\otimes[1-f]$, $W_F=(V_F\otimes V_F)/R_F$, and $\{f,g\}_F$ is the class of $[f]\otimes[g]$. Following r97, an $\mathbb F_p$-linear $\theta:V_K\to V_L$ is *compatible* if $(\theta\otimes\theta)(R_K)\subseteq R_L$; the source uses the word only for isomorphisms with equality. Put $H=K^p$ and $C=L^p$. The set $V_K$ is the point set of $\mathbb P_H(K)$, and its lines are the projective lines of 2-dimensional $H$-subspaces. For $X\in L\setminus C$, the *block* of $[X]$ is $B(X)=C(X)^\times/C^\times$.

Standing hypothesis on $L$ (only where `lem:zero-symbol` is invoked): $L/l$ is finitely generated over an algebraically closed field $l$ of characteristic $p$, the standing hypothesis of source section 2. $K$ is arbitrary.

## 1. Primary reading results

- **Carter–Vogt, PNAS 77(7):3756–3757 (1980).** Both pages were read in full from the scanned page images. The paper announces an Extension Theorem and a Characterization Theorem for lineations between affine or projective *Desarguesian planes*. Canonical types: Full (a place $\psi$, $P(\psi)$); Reduced Type 1 and 2 (prevaluation groups); special affine embeddings of order 2 and 3. No proofs appear; they are deferred to Mem. AMS 27 No. 235 (1980), which was not obtained. The source covers planes only, total maps only, and gives no multiplicative structure.
- **Machala, Čas. pěst. mat. 100 (1975) 142–154.** Read in full. Definition 3: a *homomorphism* $\chi:\mathbb P(A)\to\mathbb P(B)$ of projective spaces over division rings $F,G$, with $A$ of any dimension, satisfies three conditions:
  - (1) collinear points go to collinear points;
  - (2) every line contains three points with pairwise distinct images;
  - (3) some three images are non-collinear.

  **Theorem (p.145, proof pp.145–153).** Every homomorphism is induced by a *generalized semilinear map* $(\varphi,\sigma)$ relative to an $R$-module $W\subseteq A$. Here $R$ is a total subring of $F$ with ideal $R_0$ of non-units, $\varphi:R\to G$ is a ring homomorphism with $\ker\varphi=R_0$, and $\sigma:W\to B$ is additive with $\sigma(tw)=\varphi(t)\sigma(w)$. Every point $Fx$ has a representative in $W^*=\{w\in W:\sigma(w)\neq0\}$, and $\chi(Fw)=G\sigma(w)$ for $w\in W^*$.

  Machala cites Satz 1–2 (basic total-ring facts) to Radó. For commutative $F$ they are the standard facts that $R_0$ is the maximal ideal of the valuation ring $R$, and that finitely many nonzero $t_i$ have a common multiplier $f$ with all $ft_i\in R$ and some $ft_j=1$ (take $f=t_j^{-1}$ for $t_j$ of minimal value).
- **Havlicek, "Weak linear mappings – a survey", arXiv:1210.2053v1.** Read in full. This is navigation only. It confirms that Radó (Math. Z. 110, 1969) and Machala are the higher-dimensional non-injective theory, and that Brezuleanu–Rădulescu (J. Geom. 23, 1984) concerns full or injective lineations. Neither of those was obtained.

## 2. Proposition A (r97, recalled with a self-contained proof of the $K$-side step)

For $p=2$ and $\theta$ $\mathbb F_2$-linear, $\theta$ is compatible iff it sends every line of $\mathbb P_H(K)$ into a line of $\mathbb P_C(L)$ or to a point.

The r97 proof is unchanged. The only $K$-side input is that symbols vanish on $H(x)^\times$ for $x\notin H$: if $u,w\in H(x)^\times\setminus H^\times$ then $w=e+fu$ with $e,f\in H$. If $e\neq0\neq f$, put $q=fu/e$ (characteristic 2); then $[q]=[u]$, $[1-q]=[1+q]=[w]$, $q\neq0,1$, and $\{u,w\}_K=\{q,1-q\}_K=0$ by the defining Steinberg relation. This is the proof of `lem:affine-symbol`, valid for every field. If $e=0$, $\{u,u\}_K=\{u,-u\}_K=0$. The $L$-side uses `lem:zero-symbol` under the standing hypothesis.

**Proposition A′ (any $p$, one direction).** If $\theta$ is compatible, then every line of $\mathbb P_H(K)$ through $[1]$ is sent into $\{0\}\cup B(X)$ for some $X$. Hence every line is sent into a translate of a block, a projective $(p-1)$-space.

*Proof.* Points of the line through $[1],[x]$ are $[c+dx]$. For two such elements $u$ and $w=c''+d''u$ ($c'',d''\in H$), the same Steinberg argument gives $\{u,w\}_K=0$ when $c''d''\neq0$. When $c''=0$, $\{u,u\}=\{u,-1\}=0$, because $-1=(-1)^p$ for odd $p$. Compatibility gives $\{\theta u,\theta w\}_L=0$, and `lem:zero-symbol` puts every image class in $C(X)$ once one image $[X]\neq0$ is fixed. ∎

The converse for odd $p$ would need symbols to vanish on $C(X)^\times$ with $[C(X):C]=p\ge3$. That follows from Bloch–Kato–Gabber injectivity, which the source cites but does not prove. It is not used here.

## 3. Theorem D (author screen, $p=2$; not frozen)

**Hypotheses.** $p=2$. $K$ is any field of characteristic 2, and $L$ satisfies the standing hypothesis. $H=K^2$, $C=L^2$. $\theta:V_K\to V_L$ is $\mathbb F_2$-linear.

**Definitions.** For a valuation ring $O$ of $K$ with maximal ideal $\mathfrak m$, residue field $\kappa$, value group $\Gamma$ and valuation $v$, and a field homomorphism $\beta:\kappa\to L$:

- (BA) means every $x\in K\setminus H$ has a best approximation from $H$, i.e. $\{v(x+b):b\in H\}$ has a maximum.
- (S) means $\beta(t)\notin L^2$ for every $t\in\kappa\setminus\kappa^2$.
- If $\Gamma$ is 2-divisible, then $K^\times=H^\times O^\times$, and $\theta_{O,\beta}[hu]:=[\beta(\bar u)]$ ($h\in H^\times$, $u\in O^\times$) is a well-defined $\mathbb F_2$-linear map $V_K\to V_L$.

The conditions on $\theta$ are:

- (N) every line of $\mathbb P_H(K)$ contains three points with pairwise distinct images;
- (T) the image of $\theta$ contains two classes with nonzero symbol in $W_L$.

**Claim.** $\theta$ is compatible and satisfies (N) and (T) iff $\theta=\theta_{O,\beta}$ for a valuation ring $O$ of $K$ and a field homomorphism $\beta:\kappa\to L$ satisfying all of the following:

- $\Gamma$ is 2-divisible;
- (BA) and (S) hold;
- some $s,t\in\kappa^\times$ have $\{\beta s,\beta t\}_L\neq0$.

The pair $(O,\beta)$ is then unique.

### Proof

**Step 0: (T) is a triangle.** The image is a subgroup containing $0=[1]$. If $\{X,Y\}_L\neq0$, then $X\notin C$ and $Y\notin C(X)=C+CX$, because symbols vanish inside a block (§2). So $[1],[X],[Y]$ are non-collinear. Conversely, take a non-collinear image triple $[A_1],[A_2],[A_3]$. Multiplication by $A_1^{-1}$ is a collineation, so $[1],[A_2/A_1],[A_3/A_1]$ are non-collinear image points, and `lem:zero-symbol` gives a nonzero symbol. By Proposition A, $\theta$ is a homomorphism of $\mathbb P_H(K)$ into $\mathbb P_C(L)$ in Machala's sense: (1) is Proposition A, (2) is (N), and (3) is (T).

**Step 1: Machala data.** Machala's theorem gives $(R,\psi,W,\sigma)$. Here $R$ is a valuation ring of $H$ with maximal ideal $R_0$, $\psi:R\to C$ has kernel $R_0$, $W\subseteq K$ is an $R$-module, and $\sigma:W\to L$ is additive with $\sigma(tw)=\psi(t)\sigma(w)$. Every point has a representative in $W^*$, and $\theta[w]=[\sigma(w)]$ for $w\in W^*$. Call such a quadruple a *lift* of $\theta$.

**Lemma 1.** For $w\in W^*$, $W\cap Hw=Rw$, and $tw\in W^*\iff t\in R^\times$.

*Proof.* Suppose $t\notin R$ and $tw\in W$. Then $t^{-1}\in R_0$ and $\sigma(w)=\psi(t^{-1})\sigma(tw)=0$, a contradiction. For $t\in R$, $\sigma(tw)=\psi(t)\sigma(w)$ is nonzero iff $t\in R^\times$. ∎

**Lemma 2.** If $w,u\in W^*$ and $\theta[w]\neq\theta[u]$, then $R=\{t\in H:\theta[w+tu]\neq\theta[u]\}$.

*Proof.* Suppose $t\notin R$. Then $t^{-1}\in R_0$, so $t^{-1}w+u\in W$ with $\sigma=\sigma(u)$, and $\theta[w+tu]=\theta[t^{-1}w+u]=\theta[u]$. Suppose $t\in R$. Then $\sigma(w+tu)=\sigma(w)+\psi(t)\sigma(u)$, and $\sigma(w),\sigma(u)$ are $C$-independent, so this is not in $C\sigma(u)$. ∎

**Lemma U (uniqueness).** Let $(R_i,\psi_i,W_i,\sigma_i)$, $i=1,2$, be lifts of the same $\theta$ with some $w\in W_1^*\cap W_2^*$, and assume the image of $\theta$ has at least two points. Then $R_1=R_2$, $\psi_1=\psi_2$, $W_1=W_2$, and $\sigma_2=c\,\sigma_1$ with $c\in C^\times$.

*Proof.*

1. Since $[\sigma_2(w)]=[\sigma_1(w)]$ as $C$-lines, $\sigma_2(w)=c\sigma_1(w)$ with $c\in C^\times$.
2. Take $u\in W_1^*$ with $\theta[u]\neq\theta[w]$, and $s\in H^\times$ with $su\in W_2^*$. Lemma 2 in both lifts gives $R_2=s^{-1}R_1$.
3. Since $1\in R_2$, $s\in R_1$. Since $R_2$ is a ring, $s^{-2}\in R_2$, so $s^{-1}\in R_1$. Hence $s\in R_1^\times$ and $R_2=R_1$. Then $u\in W_2^*$ by Lemma 1.
4. Write $\sigma_2(u)=c'\sigma_1(u)$ with $c'\in C^\times$. For $t\in R$, the equality $\theta[w+tu]=[\sigma_1(w)+\psi_1(t)\sigma_1(u)]=[c\sigma_1(w)+c'\psi_2(t)\sigma_1(u)]$ and the $C$-independence of $\sigma_1(w),\sigma_1(u)$ give $c'\psi_2(t)=c\psi_1(t)$. At $t=1$ this gives $c'=c$, and then $\psi_2=\psi_1$.
5. If instead $\theta[u]=\theta[w]$, compare $u$ through a $z\in W_1^*$ with $\theta[z]\neq\theta[w]$, which was already handled. Hence $W_1^*\subseteq W_2^*$ and $\sigma_2=c\sigma_1$ there. By symmetry $W_1^*=W_2^*$.
6. For $w_0\in W_1$ with $\sigma_1(w_0)=0$, we have $w+w_0\in W_1^*$. So $w_0=(w+w_0)-w\in W_2$, and $\sigma_2(w_0)=c\sigma_1(w+w_0)-c\sigma_1(w)=0$. ∎

**Step 2: normalization.** Pick $h\in H^\times$ with $h\in W^*$. Since $\theta[h]=0$, $\sigma(h)\in C^\times$. Replace $(W,\sigma)$ by $(h^{-1}W,\ \sigma(h\,\cdot)/\sigma(h))$, which is again a lift. Now $1\in W^*$ and $\sigma(1)=1$.

**Step 3: gluing.** Take $x\in W^*$ and put $X=\sigma(x)$, so $[X]=\theta[x]$. Then $(R,\psi,x^{-1}W,\ w\mapsto X^{-1}\sigma(xw))$ is a lift of $\theta$:

- it is additive and $\psi$-semilinear;
- every point has a representative in it;
- for $w$ with $xw\in W^*$, $\theta[w]=\theta[xw]-\theta[x]=[X^{-1}\sigma(xw)]$, using that $\theta$ is a homomorphism.

Both lifts contain $1$ in their starred sets. Lemma U gives $x^{-1}W=W$ and $X^{-1}\sigma(xw)=c\sigma(w)$. Evaluating at $w=1$ gives $c=1$. Hence

$$xW=W,\qquad \sigma(xw)=\sigma(x)\sigma(w)\qquad(x\in W^*,\ w\in W).$$

Consequences:

- $W^*$ is a group: $xy\in W$ with $\sigma(xy)=\sigma(x)\sigma(y)\neq0$, and $x^{-1}=x^{-1}\cdot1\in W$ with $\sigma(x^{-1})=\sigma(x)^{-1}$.
- $W_0:=\sigma^{-1}(0)$ satisfies $W^*W_0\subseteq W_0$. It also satisfies $W_0W_0\subseteq W_0$, since $w_0w_0'=w_0(w_0'+1)-w_0$.
- So $W$ is a subring of $K$ and $\sigma$ is a ring homomorphism with $\sigma(1)=1$.
- $W$ is a valuation ring. For $y\in K^\times$ write $y=hx$ with $x\in W^*$, $h\in H^\times$. If $h\in R$ then $y\in W$; otherwise $y^{-1}=h^{-1}x^{-1}\in W$.
- $W^\times=W^*$: an element of $W_0$ cannot be a unit, since $1\notin W_0$.

Put $O:=W$, $\mathfrak m=W_0$, $\beta:\kappa\to L$ induced by $\sigma$. From $K^\times=H^\times O^\times$, $\Gamma=v(H^\times)=2\Gamma$. For $u\in O^\times$, $\theta[u]=[\sigma(u)]=[\beta\bar u]$, so $\theta=\theta_{O,\beta}$. The symbol condition is (T).

**Step 4: lines of $\theta_{O,\beta}$.** Let $\Gamma$ be 2-divisible, so $O\cap H=O^2$. Take the line through $[1]$ and $[x]$, $x\notin H$. Its points are $[1]$ and $[x+b]$, $b\in H$.

*Case A: $\{v(x+b)\}$ has a maximum at $b_0$.* Pick $h\in H$ with $v(h)$ equal to that maximum and put $u=(x+b_0)/h\in O^\times$.

- Then $\bar u\notin\kappa^2$. Otherwise $\bar u=\bar c^2$ with $c\in O^\times$, and $v(x+b_0+hc^2)$ would exceed the maximum.
- The points are $[u+e]$, $e\in H$. If $v(e)<0$, then $\theta[u+e]=\theta[1+u/e]=0$. If $e\in O^2$, then $u+e\in O^\times$ and $\theta[u+e]=[\beta\bar u+\beta\bar e]$, with $\beta\bar e\in L^2$.
- So the image is $\{0\}\cup\{[\beta\bar u+c]:c\in\beta(\kappa^2)\}$. If $\beta\bar u\in L^2$, this is the single point $0$. Otherwise $0$, $[\beta\bar u]$ and $[1+\beta\bar u]$ are pairwise distinct.

*Case B: no maximum.* For each $b$ write $x+b=h_bu_b$. If $\bar u_b\notin\kappa^2$, then $v(u_b+e)\le0$ for all $e\in H$, which would make $v(x+b)$ the maximum. So every $\bar u_b\in\kappa^2$, and the whole line maps to $0$.

Lines not through $[1]$ are translates, because $\theta$ is a homomorphism. So (N) holds iff every line is in Case A with $\beta\bar u\notin L^2$. Every $t\in\kappa\setminus\kappa^2$ occurs as such a $\bar u$: take $x=u$ with $\bar u=t$, where $b_0=0$ is the maximum. Hence

$$(N)\iff\text{(BA) and (S)}.$$

This proves "only if".

**Step 5: "if".** Given $(O,\beta)$ as stated, $\theta_{O,\beta}$ is well defined: two expressions $hu=h'u'$ give $u/u'\in O^\times\cap H=(O^\times)^2$, so $\beta(\bar u/\bar u')\in L^2$. It is compatible by r97 Proposition B. Recheck for $R_K$ generated by $[x]\otimes[1+x]$:

- if $v(x)>0$, then $\theta[1+x]=0$;
- if $v(x)<0$, then $\theta[1+x]=\theta[x]$ and $\{X,X\}=\{X,-X\}=0$, since $-1=1$;
- if $v(x)=0$ and $\bar x\neq1$, the images form a Steinberg pair $[\beta\bar x],[1+\beta\bar x]$;
- if $\bar x=1$, then $\theta[x]=0$.

(N) holds by Step 4, and (T) holds by hypothesis.

**Uniqueness.** By Step 3, any such $(O,\beta)$ gives a lift $(O\cap H,\ \beta^2\text{-place},\ O,\ \sigma)$ with $1\in O^*$ and $\sigma(1)=1$. Lemma U forces equal $O$ and $\sigma$. ∎

**Examples.**

- *Trivial valuation:* $\theta=\beta_*$ for a field embedding $\beta:K\to L$ with $\beta^{-1}(L^2)=K^2$ (for instance the identity, which covers the injective maps of `thm:main` at $p=2$).
- *Noninjective:* $K=\kappa((t^{\mathbb Q}))$, a Hahn series field with $\kappa$ imperfect satisfying the standing hypothesis (e.g. $\kappa=l(s_1,s_2)$), and $\beta=\mathrm{id}:\kappa\to L=\kappa$. Here (BA) holds because the first coefficient outside $\kappa^2$ gives the best approximation, $\Gamma=\mathbb Q$, and (S) and (T) hold. The kernel contains $(1+\mathfrak m)H^\times/H^\times\neq0$.

**Why this is a screen and not a nominee.** Step 1 is Machala's classical theorem, and Proposition A is r97. Step 3 copies the gluing used by the pinned source's own proof of `thm:main` (05-fields), which there applies `prop:projective-lift`. It compares the lifts $w\mapsto S(fw)$ and $w\mapsto S(f)S(w)$, and the same comparison works here with Lemma U in place of projective-lift uniqueness. Step 4 is elementary valuation theory. This is "a direct classical place theorem plus the pinned proof", which the r98 brief flags as making the extension technical. No contribution claim is made, and no literature search for the statement was performed.

## 4. Remaining gap after Theorem D

For $p=2$, a compatible $\theta$ with (T) either satisfies (N), and is then classified by Theorem D, or has a *collapsing line*: a line with at most two image points. In the Proposition B models, collapsing lines arise from three sources:

- $\Gamma/2\Gamma\neq0$;
- failure of (BA) (immediate-extension or defect phenomena);
- failure of (S).

Classifying the collapsing stratum is the unpaid operation. It needs a theory of lineation homomorphisms without Machala's condition (2), in arbitrary dimension, glued with the group law. The planar version is Carter–Vogt's reduced theory, announced only. Radó 1969 treats non-injective collineations of spaces under conditions that Machala describes as more restrictive than his own; it was not obtained.

**Lemma E.** Let $f$ be a map from a projective plane to a projective space sending collinear triples to collinear triples. If $f$ maps into a set $Q$ of points with no three collinear, then $|f(\pi)|\le3$.

*Proof.* Suppose $q_1,\dots,q_4$ have distinct images $P_1,\dots,P_4\in Q$. The lines $q_1q_2$ and $q_3q_4$ meet in a point $r$; they are distinct, since otherwise all four images would be collinear. The image of $q_1q_2$ is a collinear set containing $P_1,P_2$, so $f(r)$ lies on the line $P_1P_2$, and $f(r)\in Q$ forces $f(r)\in\{P_1,P_2\}$. Likewise $f(r)\in\{P_3,P_4\}$, a contradiction. ∎

**Example G (collapsing stratum with reduced planes).** Let $K=l((t))((s))$ over an algebraically closed $l$ of characteristic 2, with the rank-2 valuation, $\Gamma=\mathbb Z^2$ and perfect $\kappa=l$. Take $\theta$ from Proposition B with $\theta_G:\Gamma/2\Gamma\to V_L$ sending $v(t)\mapsto X$ and $v(s)\mapsto Y$, where $X,Y$ are 2-independent.

- The image of $\theta$ is $\{0,X,Y,X+Y\}$, a quadrangle by r97 Lemma C.
- In the plane $\mathbb P(H+Ht+Hs)$, the nonzero terms of $a+bt+cs$ have values in three distinct classes mod $2\Gamma$. So $\theta[a+bt+cs]$ is the image of the dominant term, and the plane maps onto the triangle $\{0,X,Y\}$. This matches the shape of Carter–Vogt's Reduced Type 2, with three fractional-ideal regions.
- By Lemma E, no plane of $\mathbb P_H(K)$ has more than three image points. So no full planar or Machala-type argument can start anywhere in this map.

**Example F (odd $p$: compatible but not a lineation).** For odd $p$ and any $L$, $\theta=2\cdot\mathrm{id}_{V_L}$ is compatible, since $(\theta\otimes\theta)(R_L)=4R_L$. It sends the collinear points $[1],[x],[1+x]$ ($x\notin C$) to $[1],[x^2],[(1+x)^2]$. These are not collinear, because $1,x,x^2$ are $C$-independent when $[C(x):C]=p\ge3$ (`lem:p-basis`). So for odd $p$ even bijective compatible maps are not lineations, which is the source's $\Lambda^\times$ ambiguity. A noninjective odd-$p$ theory needs Proposition A′'s block geometry first.

## Novelty limits

Nothing here is claimed new to the literature. Theorem D is a composition of a classical theorem (Machala 1975) with the pinned proof's gluing step and elementary valuation theory. Lemma E and Examples F and G are elementary. "New to this project" means only that r24 and r97 did not state them.
