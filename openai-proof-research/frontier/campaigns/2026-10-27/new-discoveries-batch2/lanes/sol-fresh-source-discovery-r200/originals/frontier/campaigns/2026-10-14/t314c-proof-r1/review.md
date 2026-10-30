# T314C independent full-scope proof review, round 1

Reviewer: independent proof-review sub-agent (Claude Opus 5.5 via Factory/T3 Code), fresh first review. This is not an acceptance decision, contribution verdict, manuscript gate or formal gate. Count stays at 14. No nested agents, shared-ledger edits, staging, commits, author-packet changes or uploads. Scratch work was confined to `/var/tmp/t314c-r1/`. The parallel reviewer's report was not read.

## Verdict

**Mathematical verdict: PASS_FULL_T314C.**

Every quantifier and conclusion of the frozen `original-scope.md` (SHA256 `676eed91…e29e`) is proved by `candidate.md` (SHA256 `7bc61c8a…eaea9`), given the stipulated source314 `thm:main` at pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. I rederived each step independently (Section 3). I found no blocking gap and no counterexample. The target was not narrowed. There are **no required objections**; six optional presentation objections are listed in Section 5.

Separate gates, not decided here:

- **Contribution:** not assessed. The proof's new step uses only the Frattini count, the containment of $[H,H]$ in $K$ for a cyclic quotient, and the maximal isotropic dimension of an alternating form. Whether that is a substantial contribution belongs to the separate contribution gate. Nothing in this review supports a substantiality or priority claim.
- **Formal / manuscript / release:** not assessed. No Lean or manuscript exists in the packet.

## 1. Inputs authenticated before trust

| Item | Expected (external) | Observed |
|---|---|---|
| Author `MANIFEST.json` | `b8b77b3b52e977ca3abd1ce9167ca605c2dae722f855e7b2ff67c43b5826ff4a` | match |
| `candidate.md` | `7bc61c8a0949c671a5f8dd8b9f55502e1b526ed40968dc0912be984f789eaea9` | match |
| `original-scope.md` | `676eed9172e85a2c99a7ff52dbe911cae036c104dba0bb409a2b158e4791f29e` | match |
| `sources/preprints-tree.json` | `eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b`, 13223 entries, `truncated=false` | match |

All 34 manifest payloads hash correctly, with no extra or missing files and no symlinks. All 12 non-PDF source314 blobs under `preprints/Cyclic-Length-and-Chromatic-Fixed-Point-Loss-September-24-2026/` have Git blob SHA1 and size equal to their canonical tree entries, with pinned raw URLs. `01-introduction.tex` is blob `cb2ae4e2…`, as the candidate cites. My own `pdftotext` extractions of the three retained primary PDFs are byte-identical to the author's text files. The checker is `review_check.py`, written from scratch; it imports nothing from the author packet.

## 2. Exact source interface used

From `01-introduction.tex` (read in full): for a prime $p$, finite $p$-group $G$, $H\le G$, $n\ge0$, $r_n(G,H)$ is the **least** nonnegative $r$ such that $K(n+r)_*(\Phi^H X)=0\Rightarrow K(n)_*(\Phi^G X)=0$ for every finite $p$-local genuine $G$-spectrum $X$. Here "finite spectra include compact retracts" and $K(0)=H\mathbb Q$. $\ell(G,H)$ is the least length of a subnormal chain $H=G_0\trianglelefteq\cdots\trianglelefteq G_s=G$ with cyclic quotients. `thm:main`: $r_n(G,H)=\ell(G,H)$ for every $p$, $G$, $H$, $n\ge0$. The text following it states the witness form: for every integer $0\le r<\ell(G,H)$ there is a finite genuine $G$-spectrum with $K(n+r)$-acyclic $\Phi^H$ and $K(n)_*(\Phi^G)\ne0$. `02-background.tex` (read in full) fixes $p$-local genuine spectra, compact objects as retracts of finite $G$-CW spectra, and Proposition `prop:cyclic-upper`. The scope's definitions of $\ell$ (normality only in the next group) and $r_h$ agree with these.

## 3. Independent rederivation

Notation: $\bar{\ }:R\to L$ is reduction, $i:L\to pR$ is $v\mapsto p\cdot(\text{lift})$, $c(x,y)=i(\tfrac12\beta(\bar x,\bar y))$, and $p$ is odd.

**3.1 Group, cocycle, powers, commutator.** $i$ is well defined because $p\cdot pR=0$, and it is an additive isomorphism $L\to pR$. Bilinearity gives
$c(x,y)+c(x+y,z)=i(\tfrac12[\beta(x,y)+\beta(x,z)+\beta(y,z)])=c(y,z)+c(x,y+z)$.
Since $c$ depends only on residues and $\overline{c(\cdot,\cdot)}=0$,
$(x*y)*z=x+y+z+c(x,y)+c(x+y,z)$ and $x*(y*z)=x+y+z+c(y,z)+c(x,y+z)$, so the product is associative. The identity is $0$ because $c(0,\cdot)=c(\cdot,0)=0$, and $x*(-x)=c(x,-x)=-\tfrac12 i\beta(\bar x,\bar x)=0$. By induction, $x^{m+1}=mx+x+i(\tfrac m2\beta(\bar x,\bar x))=(m+1)x$. Hence $x^p=px=i(\bar x)$. Also $p^2x=0$, and $px=0\iff x\in pR$. So the order is $p^{2d}$, the exponent is exactly $p^2$ (since $d\ge1$), and $\Omega_1=pR$.

Elements $z\in pR$ satisfy $c(z,\cdot)=c(\cdot,z)=0$, so $pR$ is central and its group law is addition: it is elementary abelian of rank $d$. Since $\overline{x*y}=\bar x+\bar y$, $\bar{\ }$ is a homomorphism. The map $x\mapsto x^p=i(\bar x)$ is a surjective homomorphism $G\to pR$ with kernel $pR$, so it induces the isomorphism $G/pR\to pR$ given by $i$ (scope item). Moreover $y*x=x+y-\tfrac12 i\beta$, so $x*y=(y*x)*i(\beta(\bar x,\bar y))$ with a central correction. Hence $[x,y]=xyx^{-1}y^{-1}=(xy)(yx)^{-1}=i(\beta(\bar x,\bar y))$. Then $[G,G]\le pR=G^p\le Z(G)$, the class is at most 2, $G$ is powerful (odd-$p$ definition), and $\Phi(G)=G^p[G,G]=pR$. For $\beta=0$ the group is $(\mathbb Z/p^2)^d$, which has class 1. These checks were also confirmed exhaustively on the finite cases (Section 4). Associativity was sampled there, with the cocycle identity checked exhaustively.

**3.2 Subgroups, U/W rank, all sections.** For $H\le G$, $U_H=\bar H$ is a subgroup of an elementary abelian group, hence a subspace, and $W_H=i^{-1}(H\cap pR)$ is likewise a subspace. The sequence $1\to H\cap pR\to H\to U_H\to0$ gives $|H|=p^{\dim U_H+\dim W_H}$. The set of $p$th powers of $H$ is $i(U_H)$, the image of a homomorphism. So $H^p=i(U_H)\le H\cap pR$, which gives $U_H\subseteq W_H$ and $|H/H^p|=p^{\dim W_H}$. Then $H^p\le\Phi(H)$ and Burnside's basis theorem give $d(H)=\log_p|H/\Phi(H)|\le\dim W_H\le d$. For $N\trianglelefteq H$, $d(H/N)\le d(H)$. The section $S=pR$, $N=1$ attains $d$. So the sectional rank is exactly $d$ for every $\beta$, and no assumption that $H$ is graded, powerful or of type $(2,\dots,2)$ is used.

**3.3 Arbitrary cyclic subnormal chain.** Any chain of minimal length is strict, because repeated terms can be deleted, so it suffices to bound strict chains $1=H_0\triangleleft H_1\triangleleft\cdots\triangleleft H_k=G$ with each $H_{j-1}\trianglelefteq H_j$ only. Each factor is a nontrivial cyclic subquotient of an exponent-$p^2$ group, so it has order $p$ or $p^2$. With $s$ factors of order $p^2$ and $t$ of order $p$, $2s+t=2d$ and $k=s+t=2d-s$.

At an order-$p^2$ step $K\trianglelefteq H$ with $H/K=\langle gK\rangle$, we have $g^p\notin K$. If $\bar g=\bar k$ for some $k\in K$, then $g^p=i(\bar g)=i(\bar k)=k^p\in K$, a contradiction. Since $\bar{\ }$ is a homomorphism and $H=\langle K,g\rangle$, $U_H=U_K\oplus\mathbb F_p\bar g$, so $\dim U$ rises by exactly one. Because $|H:K|=p^2$, $\dim W$ also rises by exactly one. Since $K\subseteq H$, $U$ and $W$ never decrease along the chain, so intervening order-$p$ steps cannot lower them. Hence at the top $H$ of the **last** order-$p^2$ step, $\dim U_H\ge s$.

At that step, $\dim W_K=\dim W_H-1\le d-1$, so some $f\ne0$ in $L^*$ vanishes on $W_K$. Since $H/K$ is cyclic, hence abelian, and $K\trianglelefteq H$, we get $[H,H]\le K$. By 3.1 the commutators also lie in $pR$, so $i(\beta(U_H,U_H))\subseteq K\cap pR=i(W_K)$. Thus $U_H$ is totally isotropic for $B_f=f\circ\beta$.

Isotropic bound: let $\operatorname{rank}B_f=2a$ and $\mathrm{Rad}=\mathrm{Rad}\,B_f$, so $\dim\mathrm{Rad}=d-2a$. Then $(U_H+\mathrm{Rad})/\mathrm{Rad}$ is isotropic in a nondegenerate $2a$-dimensional symplectic space, so its dimension is at most $a$. Hence $\dim U_H\le a+(d-2a)=d-a\le d-\rho$, since $a\ge\rho$ by the definition of $\rho$ as a minimum. Therefore $s\le d-\rho$ and $k\ge d+\rho$. If $s=0$, then $k=2d\ge d+\rho$ because $\rho\le d/2$. So $\ell(G_\beta,1)\ge d+\rho(\beta)$.

The only normality used is $K\trianglelefteq H$ at a single step. Centrality of $pR$ is a property of $G$, not an assumption about the chain. No global-normality, central-series, powerful-subgroup or graded-subgroup assumption appears. The finite data show this distinction matters: for two random $\beta$ at $(p,d)=(3,3)$, chains of subgroups normal in $G$ need length 4, while subnormal chains reach length 3.

**3.4 Finite-field family, including $p\mid d$.** Take $L=\mathbb F_{p^d}$, $d$ odd, $d\ge3$, and $\beta(x,y)=xy^p-x^py$. This map is $\mathbb F_p$-bilinear and alternating. Every functional is $\mathrm{Tr}(a\,\cdot)$ with $a$ unique, because the trace pairing of the separable extension $\mathbb F_{p^d}/\mathbb F_p$ is nondegenerate regardless of whether $p\mid d$; only $\mathrm{Tr}(1)$ vanishes then, and that is irrelevant. Frobenius invariance gives $\mathrm{Tr}(axy^p)=\mathrm{Tr}((ax)^{p^{d-1}}y)$, so $\mathrm{Rad}\,B_a=\{x:(ax)^{p^{d-1}}=ax^p\}$. Raising to the $p$th power is bijective, so this set equals $\{x:ax=a^px^{p^2}\}$. For $x\ne0$ the condition is $x^{p^2-1}=a^{1-p}$. In the cyclic group of order $N=p^d-1$, $\gcd(p^2-1,N)=p^{\gcd(2,d)}-1=p-1$. Since $(a^{1-p})^{N/(p-1)}=a^{-N}=1$, $a^{1-p}$ lies in the image of the $(p^2-1)$-power map, so there are exactly $p-1$ solutions. Hence $|\mathrm{Rad}|=p$, $\operatorname{rank}B_a=d-1$ for every $a\ne0$, and $\rho=(d-1)/2$. This matches Gow–Quinlan Lemma 3 / Theorem 1 with $\sigma$ the Frobenius of odd order $d$, giving rank $n-n/(2r+1)=d-1$; I read their actual text.

The common radical of $\beta$ is zero: for $x\ne0$ and $z\notin\mathbb F_p$ (which exists because $d>1$), $\beta(x,xz)=x^{p+1}(z^p-z)\ne0$. Hence $x$ is central iff $\beta(\bar x,\cdot)=0$ iff $x\in pR$, so $Z(G)=pR$. If $\operatorname{span}\beta(L,L)\ne L$, some $f\ne0$ would give $B_f=0$, contradicting rank $d-1\ge2$. So $[G,G]=i(L)=pR$. Thus $Z=G^p=\Phi=[G,G]=pR$, the class is exactly 2, the sectional rank is $d$, and $\ell\ge d+(d-1)/2=(3d-1)/2$, with excess $(d-1)/2$ over sectional rank for each fixed odd $p$.

**3.5 Source314 application, all heights.** $G_{(p,d)}$ is a finite $p$-group, and $H=1$ is a subgroup. By `thm:main`, $r_h(G,1)=\ell(G,1)\ge(3d-1)/2$ for every $h\ge0$, including $h=0$ with $K(0)=H\mathbb Q$. For an integer $0\le t<(3d-1)/2\le r_h$, minimality of the least integer $r_h$ means the implication fails at $r=t$. So there is a finite $p$-local genuine $G$-spectrum $X$, in the source convention that includes compact retracts, with $K(h+t)_*(\Phi^1X)=0$ and $K(h)_*(\Phi^GX)\ne0$. This is also the source's displayed witness sentence. The case $t=0$ is included. No cell bound, sharpness, or bounded-size claim is made, and none is needed.

## 4. Scope coverage (quantifier by quantifier)

| Scope claim | Status |
|---|---|
| All odd $p$, all $d\ge1$, all $L$, all alternating $\beta$, any basis | proved (3.1–3.3; the basis enters only through the identification) |
| Powerful, exponent $p^2$, order $p^{2d}$, central elementary abelian $pR$, $p$th-power isomorphism $G/pR\to pR$ via $i$ | proved (3.1) |
| Sectional rank exactly $d$ (all $N\trianglelefteq S\le G$) | proved (3.2) |
| $\ell(G_\beta,1)\ge d+\rho(\beta)$ for arbitrary cyclic subnormal series, including intervening order-$p$ steps and nongraded subgroups | proved (3.3) |
| Class 1 for $\beta=0$, class at most 2 in general; $pR$ need not equal the center | proved (3.1) |
| Family: every odd $p$, every odd $d\ge3$: $Z=G^p=\Phi=[G,G]=pR$, sectional rank $d$, $\ell\ge(3d-1)/2$, excess $\ge(d-1)/2$, trace-form rank exactly $d-1$ | proved (3.4), including $p\mid d$ |
| For all $h\ge0$: $r_h\ge(3d-1)/2$; for every integer $0\le t<(3d-1)/2$ an existential witness, including $h=0$ and compact retracts | proved from the stipulated `thm:main` (3.5) |

## 5. Objections

**Required: none.**

**Optional (presentation only; none affects validity):**

1. §3 should say in one sentence that minimal chains are strict, so restricting to strict chains loses nothing.
2. §1 states $x^p=i(\bar x)$, but not in words the scope item "the $p$th-power isomorphism $G/pR\to pR$ induced by $i$". Add: $x\mapsto x^p$ is a surjective homomorphism with kernel $pR$.
3. §3, "dim U_H ≥ s": state that $U$ never decreases and rises by exactly one at each order-$p^2$ step, so all $s$ increases are counted by the last one. The text implies this but compresses it.
4. §3, the parenthetical "one may choose $f(\bar g)\ne0$" is correct but unused. Mark it as a remark or drop it.
5. §5 could cite the minimality of $r_h$ (or the source's own witness sentence) explicitly as the reason for existence. If an honest finite $G$-CW witness is ever wanted, rather than a compact retract, $X\oplus\Sigma X$ has the same $K$-homology vanishing pattern and, by Thomason's theorem, lies in the finite subcategory. This is outside the frozen scope and is optional.
6. §2, "$H^p$ generated by powers equals $i(U)$": note that the set of $p$th powers is already a subgroup because the power map is a homomorphism.

There are no prior review-round objections to carry forward; this is round 1.

## 6. Finite diagnostics and controls (identity and implementation only; not proof)

`review_check.py` requires the external author-manifest hash in every mode and verifies it before reading any other content. Results are saved here.

- `identity-result.json`: 34 payloads and 12 canonical source blobs verified; the `thm:main` text is present in the authenticated blob.
- `control-results.json`: a positive baseline plus 12 rejected integrity controls, each with an exact expected reason. The controls cover a wrong anchor, a malformed anchor, a flipped candidate byte, a flipped candidate byte with a resealed manifest (caught by the external candidate hash), a flipped scope byte with a resealed manifest, an extra file, a missing file, a symlink, a flipped tree byte, a source edit turning `=` into `\le` in `thm:main` with resealed receipts (caught by the canonical Git blob), an unpinned URL, and a dropped source receipt. Additional manual checks: the finite mode rejects a wrong anchor, and the controls mode rejects scratch outside `/var/tmp/`.
- `finite-results.json`: black-box computations that do not use the candidate's U/W parametrization. Subgroups are enumerated by adjoining normalizing elements $g$ with $g^p\in M$, which is complete for $p$-groups. The enumeration is cross-checked by Frobenius counts $\equiv1\pmod p$ and the number of order-$p$ subgroups. Exact $\ell$ is computed by dynamic programming over all subnormal cyclic edges, and the optimal chain is re-verified step by step from the multiplication table. Results: Gow–Quinlan $(3,3)$ has 364 subgroups, 954 order-$p^2$ cyclic edges, $\rho=1$ and exact $\ell=4$, equal to the bound. Abelian $(3,3)$ gives $\ell=3$. Three random $(3,3)$ and two random $(5,2)$ forms satisfy $\ell\ge d+\rho$. On every cyclic order-$p^2$ edge, the $U$-jump and $\beta(U_H,U_H)\subseteq W_K$ were checked. The commutator and power identities were checked on all element pairs and all elements; the cocycle identity was checked exhaustively on residues, and associativity on 20000 random triples per case. Five negative controls are rejected as expected: the mutated bound $d+\rho+1$; a non-bilinear correction that fails the cocycle identity; a symmetric $\beta$ that fails the commutator identity; a dropped subgroup that fails the counts; and ignoring cyclicity, which yields $\ell=3$ below the bound and so shows the cyclic test is essential.

The 364 subgroups and 954 order-$p^2$ edges agree with the author's README. I did not run or read the author's `diagnostics.py`, `controls.py`, `diagnostic-results.json` or `control-results.json`.

Replay from the repository's `openai-proof-research/` directory:

    python -B frontier/campaigns/2026-10-14/t314c-proof-r1/review_check.py {identity|finite} --expected b8b77b3b52e977ca3abd1ce9167ca605c2dae722f855e7b2ff67c43b5826ff4a --packet frontier/campaigns/2026-10-14/fresh-structural-discovery-r66 --tree "$PWD/sources/preprints-tree.json"
    ... controls ... --scratch /var/tmp/<dir>
    python -B frontier/campaigns/2026-10-14/t314c-proof-r1/review_check.py review-identity --expected <external REVIEW-MANIFEST.json SHA256>

## 7. Reading limits

Read in full: `candidate.md`, `original-scope.md`, `comparison.md`, `reading-limits.md`, `README.md`, `preflight.md`, `scope-freeze.txt`, `MANIFEST.json`, `source-receipts.json`, `primary-receipts.json`, `private/README.md`, the author's `verify.py`, and `AGENTS.md`. I also read `VALIDATION.md`, but its middle was truncated in display; the visible rules are the ones relied on.

Partially read:

- `frontier/NEW-TEN-2026-10-14.md`: lines 1–80 (acceptance and publication rules), plus a keyword scan.
- Source314: `01-introduction.tex` and `02-background.tex` in full. The other ten authenticated files were not semantically read; source truth is stipulated.
- Gow–Quinlan (own extraction, identical to the author's): text lines 20–269, covering the definition of $f_{b,\sigma}$, Lemmas 1–4, Corollaries 1–2 and the Theorem 1 statement.
- de las Heras–Traustason (own extraction): lines 995–1184, covering §6 from Proposition 6.1 through Corollary 6.10 and the opening of §7.
- Kuhn–Lloyd: a keyword scan only (Definition 2.5, the $r_\pm$ lines). Not read as a body, and not needed for the proof.
- The author's `controls.py`: a header scan only.

Not read: `discovery-r66-parent/chain-obstruction.md` (author collaboration, not a proof dependency), the parallel reviewer's report, the author's diagnostics, and any literature beyond the above. No web search was performed.

## 8. Boundaries

PASS_FULL_T314C is a mathematical proof verdict on the frozen scope, relative to stipulated source314 truth. It does not certify contribution, novelty or priority. It does not cover manuscript quality, formalization or release readiness. It does not change the count. Finite results and hashes certify identity and implementation only.
