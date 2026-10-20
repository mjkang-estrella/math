# Arithmetic r97: public report

Status: PREFREEZE. No frozen target, no author proof, no nominee. No mathematical gate, contribution gate or count is assigned by this round.

Runner: Factory Droid / claude-opus-5-5 / high. Pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Main direction: family 009, compatible homomorphisms of mod-$p$ Milnor $K$-theory

Source: `preprints/Reconstruction-from-Milnor-K-theory-modulo-the-characteristic-October-5-2026/build/build/` (`main.tex`, sections 01-05, `references.bib`; all read in full, all blob-checked). Labels used: `thm:main`, `lem:p-degree`, `lem:p-basis`, `lem:zero-symbol`, `lem:affine-symbol`, `prop:intersection`, `lem:scalar-line`, `prop:lines`, `prop:projective-lift`, `lem:perfect-core`.

Notation follows the source. For a field $F$ of characteristic $p$: $C_F=F^p$, $V_F=F^\times/F^{\times p}$, $R_F\subset V_F\otimes V_F$ the span of Steinberg tensors, $W_F=(V_F\otimes V_F)/R_F$, $\{f,g\}_F$ the class of $[f]\otimes[g]$. A $\Lambda$-linear map $\theta:V_K\to V_L$ is *compatible* if $(\theta\otimes\theta)(R_K)\subseteq R_L$. For $X\in L\setminus C_L$, the *block* of $[X]$ is $B(X)=C_L(X)^\times/C_L^\times\subset V_L$.

The family's open frontier, recorded by r24 (`r24-screen-009.md`), is the classification of noninjective compatible maps. r24 found valuation-type examples, an inseparable-embedding example, and named the unpaid bridge: a plane-by-plane classification of collapsed configurations, then a global valuation structure with exponent-$p$ value groups. This round tried to shrink that gap. It did not close it.

### Proposition A (characteristic 2: compatibility is a homomorphic lineation)

Hypotheses: $p=2$; $K$ any field of characteristic 2; $L/l$ a finitely generated extension of an algebraically closed field of characteristic 2 (the standing hypothesis of source section 2; the argument uses only $[L:L^2]<\infty$). $\theta:V_K\to V_L$ is $\mathbb F_2$-linear. Put $H=K^2$, $C=L^2$.

Claim. The following are equivalent.

1. $\theta$ is compatible.
2. For every $x\in K\setminus H$, $\theta\bigl(H(x)^\times/H^\times\bigr)$ is $\{0\}$ or is contained in a single block of $V_L$.
3. $\theta$, viewed as a map $\mathbb P_H(K)\to\mathbb P_C(L)$, sends every projective line either into a projective line or to a single point.

Proof.

*Blocks are lines through $[1]$.* For $x\notin H$, `lem:p-basis` (stated for any field) gives $[H(x):H]=2$, so $H(x)=H+Hx$ and $H(x)^\times/H^\times$ is the projective line through $[1]$ and $[x]$. The same holds in $L$.

*Symbols vanish inside a block (any field $F$ of characteristic 2).* Let $u,w\in C_F(s)^\times$ with $s\notin C_F$. If $u\in C_F$ or $w\in C_F$, one class is $0$. Otherwise $C_F+C_Fu=C_F(s)$, so $w=e+fu$ with $e,f\in C_F$, $f\neq0$. If $e\neq0$, `lem:affine-symbol` gives $\{u,w\}_F=0$ (its proof uses only $C=F^p$). If $e=0$, $\{u,w\}_F=\{u,u\}_F=\{u,-u\}_F=0$, using $-u=u$ and Milnor's identity $\{u,-u\}=0$ in $K_2^M(F)$, which the source identifies with $W_F$ modulo $p$.

*(1)⇒(2).* Fix $x\notin H$ and $S=\theta(H(x)^\times/H^\times)$. For $u,w\in H(x)^\times$ the previous paragraph gives $\{u,w\}_K=0$, so $[u]\otimes[w]\in R_K$ and, by compatibility, $\{\theta u,\theta w\}_L=0$. If $S\neq0$, pick $[X]\in S$ nonzero, so $X\notin C$. For any $[Y]\in S$, `lem:zero-symbol` (applied in $L$) gives $Y\in C(X)$. Hence $S\subseteq B(X)$.

*(2)⇒(1).* $R_K$ is spanned by $[x]\otimes[1-x]$, $x\neq0,1$. If $x\in H$ both $[x]$ and $[1-x]=[1+x]$ vanish. If $x\notin H$, both lie in $H(x)^\times/H^\times$, so their images are $0$ or lie in one block; symbols vanish inside a block, so the image tensor lies in $R_L$.

*(2)⇔(3).* A line through distinct points $[s],[t]$ is $\{[as+bt]\}=[s]+H(t/s)^\times/H^\times$ in the group $V_K$. Its image is $\theta[s]+\theta(H(t/s)^\times/H^\times)$. Under (2) this is a point or lies in $\theta[s]+B(W)$, which is the multiplicative translate by a representative of $\theta[s]$ of the line through $[1]$ and $[W]$, hence a line. Conversely (3) applied to lines through $[1]$ gives (2): the image contains $\theta[1]=[1]$, a point image is then $\{0\}$, and a line of $\mathbb P_C(L)$ containing $[1]$ is a block. ∎

Consequence. For $p=2$ the "collapsed configuration" problem of r24 disappears at the level of lines: every compatible map, injective or not, is a group homomorphism $\mathbb P_H(K)\to\mathbb P_C(L)$ that preserves collinearity. For odd $p$ blocks are $(p-1)$-dimensional projective spaces, not lines, and the source needs `prop:intersection` with nonmonomial images to recover lines; in noninjective maps those images can collapse (example below), so these arguments give no analogue of Proposition A there.

### Proposition B (model compatible maps, every $p$)

Hypotheses: $K,L$ any fields of characteristic $p$; $v$ a valuation on $K$ with ring $O$, maximal ideal $\mathfrak m$, residue field $\kappa$; $\beta:\kappa\to L$ a field homomorphism. Put $G=K^\times/(1+\mathfrak m)K^{\times p}$.

Claim. The map $\kappa^\times/\kappa^{\times p}\to G$ induced by $O^\times\to K^\times$ is injective, and for every $\mathbb F_p$-linear $\theta_G:G\to V_L$ extending $[\bar u]\mapsto[\beta(\bar u)]$, the composite $\theta:V_K\to G\to V_L$ is compatible.

Proof. Injectivity: if $u\in O^\times$ equals $(1+m)w^p$, then $v(w)=0$ and $\bar u=\bar w^p$. Compatibility, for $x\neq0,1$: if $v(x)>0$ then $1-x\in1+\mathfrak m$ and $\theta[1-x]=0$. If $v(x)<0$ then $1-x=-x(1-x^{-1})$ with $1-x^{-1}\in1+\mathfrak m$, so $\theta[1-x]=\theta[x]+[\beta(-1)]=\theta[x]$, because $-1$ is a $p$th power for odd $p$ and equals $1$ for $p=2$; then $\{X,X\}_L=\{X,-1\}_L=0$. If $v(x)=0$ and $\bar x\neq1$, the images are $[\beta\bar x]$ and $[1-\beta\bar x]$, a Steinberg pair. If $\bar x=1$, then $\theta[x]=0$. ∎

This family contains r24's $\psi_h$ examples, its inseparable embedding $z\mapsto z^p$ (trivial valuation, $\beta$ not onto), and pure value-group maps: for a rank-two valuation with perfect residue field, $V_\kappa=0$ and $\theta_G$ is any linear map $\Gamma/p\Gamma\to V_L$; sending the two generators of $\Gamma/p\Gamma\cong\mathbb F_p^2$ to a $p$-independent pair gives a compatible map with nondegenerate image (two classes with nonzero symbol) whose residue part is zero. So a classification cannot say "nondegenerate implies the induced residue map is a field-homomorphism map"; the residue part may itself be degenerate.

Collapse example for odd $p$: take $v$ discrete with uniformizer $\pi$ and $\theta_G$ sending $[\pi]$ to a nonzero class $T$. For $a\in H^\times$ we have $v(a)\in p\mathbb Z$. If $v(a)>0$ then $(\pi+a)/\pi\in1+\mathfrak m$, so $\theta[\pi+a]=T$; if $v(a)\le0$ then $(\pi+a)/a\in1+\mathfrak m$, so $\theta[\pi+a]=0$. Thus for $x=\pi$ every point $u=x+a$ of the source affine configuration in `prop:lines` has image in $\{0,\theta[x]\}\subset\mathbb F_p\theta[x]$, and the nonmonomial hypothesis of `prop:intersection` fails for every $a$, even when the image of $\theta$ is nondegenerate elsewhere.

### Lemma C (nondegeneracy gives a quadrangle, $p=2$)

If $X,Y\in L$ are 2-independent over $C$, the points $[1],[X],[Y],[XY]$ of $\mathbb P_C(L)$ have no three collinear. Proof: each of $Y\in C+CX$, $XY\in C+CX$, $XY\in C+CY$ and $XY\in CX+CY$ forces $Y\in C(X)$ (for the last, $XY=aX+bY$ gives $(X-b)(Y-a)=ab$, and $ab=0$ also gives dependence). ∎ So under Proposition A a compatible map whose image contains two classes with nonzero symbol is a collinearity-preserving group homomorphism whose image contains a quadrangle.

### Strongest reduction reached

For $p=2$, Proposition A and Lemma C reduce the nondegenerate noninjective classification of family 009 to the following statement, which was not proved here. Its conclusion is the converse shape of Proposition B; whether it is even true as stated was not settled.

> (Place statement, not frozen.) Let $\phi:\mathbb P_H(K)\to\mathbb P_C(L)$ be a collinearity-preserving group homomorphism ($H=K^2$, $C=L^2$) whose image contains a quadrangle. Then there is a valuation $v$ of $K$ with $\phi(1+\mathfrak m_v)=0$ such that $\phi$ restricted to $O_v^\times$ factors through $\kappa_v^\times/\kappa_v^{\times2}$, and the induced map is either induced by a field homomorphism $\kappa_v\to L$ or has image in one block.

The unpaid nonroutine operation is the construction of the valuation ring from collinearity alone, a Carter-Vogt type "lineations are induced by places" theorem adapted to multiplicative group structure and to two different coordinate fields $H\neq C$. Lineation theory (Carter-Vogt, Radó, Brezuleanu-Rădulescu) was located by web search only. Its bodies were not acquired or read, so no exact statement is relied on. The mod-$p$ value group also blocks the torsion-free descent r24 identified in the characteristic-zero primary. For odd $p$ the operation is larger: Proposition A itself fails to have an analogue, so a collapse classification is needed first.

Attempts that did not close the gap:

- Rigid-element constructions (Arason-Elman-Jacob, Koenigsmann style) need a subgroup $T\le K^\times$ with $1+x\in T\cup xT$ outside $T$. With $T=\theta^{-1}(U)$ this needs a subspace $U$ of the image meeting every block in codimension at most one. That exists in the value-group part of the model maps but not in the residue part (it fails already for the identity of $V_K$), so it can at best recover the value-group layer.
- Efrat-style graph criteria on $K^M(K)/S$ with $S=\ker\theta$: image classes in different blocks always give nonzero symbols, so the graph is complete multipartite with diameter at most two, below the diameter-four threshold.

### Base-free reading of `thm:main` (screened, TECHNICAL, not frozen)

Inspection of the source proofs shows where the finitely-generated and algebraically-closed hypotheses enter. `lem:p-degree` is used only to get $p^2\le[F:F^p]<\infty$. `lem:p-basis`, `lem:zero-symbol` and `prop:intersection` need only $[F:F^p]<\infty$. `prop:projective-lift` is for any finite-dimensional spaces. `lem:perfect-core` is used only to show $S(k)=l$. Hence the source proof, read with these hypotheses, gives: for fields $K,L$ of characteristic $p$ with $p^2\le[K:K^p]<\infty$ and $p^2\le[L:L^p]<\infty$, the map $\operatorname{Isom}(K,L)\to\operatorname{Isom}_{\mathrm M}(V_K,V_L)/\mathbb F_p^\times$ is bijective. This is a hypothesis relaxation that reuses every source operation, so it is not a candidate. No proof is written for it here and no literature-priority claim is made.

## Other screen

Family 004 (Hilbert's tenth problem over $\mathbb Q$): an extension to number fields would need the rank-one elliptic group, the five-point height estimate and the prime-pattern theorem over $K$, each a central input of the source. That is a full rerun of the source, not a compatibility operation. History hits: r63 (T004Q63 smooth-quartic scope, unresolved), r72 recovery (T242Z). No new mathematical work was done on it.

See `screens.md` for the history-only families and `reading-limits.md` for read extents.

## Novelty limits

Propositions A and B and Lemma C are elementary and new to this project's record only in the sense that r24 did not state them. No literature search beyond navigation was performed for them; mod-2 Milnor $K$-theory in characteristic 2 and valuation-type maps are classical topics. Nothing here is a demonstrated new-to-literature theorem.
