# Other screens (all stopped before any freeze)

Families were chosen from `private/history/family-history-counts.txt`. That file counts authored history units per catalogue family; 017, 016, 037, 041 and 062 were among those with zero or one units. The excluded families listed in the brief were not touched. Every source body named below is a pinned raw file recorded in `source-register.json`. Unless stated otherwise, a file listed as read was read in full.

## 017 — irrationality exponent of π

- **Read.** `main.tex` (`thm:main`, line 64: $\mu(\pi)=2$ with an ineffective $Q(\nu)$), `interpolation.tex` (`geom:interpolation`, line 25; `geom:curve-inequality`, line 242), `determinant.tex` (`det:comparison`, line 353), `series.tex`, `conclusion.tex` (`par:constants`, line 9), `references.bib` and `README.md`.
- **Mechanism.** Separated-weight interpolation, then an arithmetic/collision determinant comparison, then parameter choice. The proof uses the specific fiber and centre structure attached to π.
- **History.** I81 recorded only the open effectivity question, and r72 rejected the family at catalogue level. No authored log-α or arctangent work was found.
- **External navigation** (search snippets and abstracts only; not semantic reads and not priority clearance):
  - arXiv:2610.10192v2 (Liu–Jiang–Zhang) states $\mu(\log r)=2$ for every rational $r>0$, $r\ne1$, using moving-centre interpolation.
  - Casper preprints state exponent 2 for nonzero rational arctangents, for $\arctan(\sqrt2)/\sqrt2$ and for $\log(3+2\sqrt2)/\sqrt2$, and exponent at most 4 for positive quadratic logarithms.
  - formal-conjectures issues #6899, #6924, #6927, #6929 and #6941 track these.
- **Stop.** The natural source-mechanism extensions (rational logarithms, arctangents) are claimed externally. The remaining general case (exponent 2 for a general real-quadratic or algebraic logarithm) needs a new collision estimate for which no closable route was found. That is a hard central gap, not a closable operation.

## 016 — Zilber–Pink (abelian; curves in $A^2$)

- **Read.** Both introductions.
- **Stop.** The natural "characteristic-zero from $\overline{\mathbb Q}$" extension is the Barroero–Dill reduction (arXiv:1909.01271, navigation only). The abelian source already uses Barroero–Dill's optimal-subvariety reduction (01-introduction.tex, line 74) and Dill's generalized Vojta–Rémond inequality (lines 179–182). The extension is paid.

## 037 — ordinary-double-point / normalized-volume gap

- **Read.** Introduction and conclusion.
- **Stop.** The global consequence is already in the source. `cor:global` (line 64) gives the bound $(-K_V)^n\le 2((n^2-1)/n)^n$ for singular K-semistable Q-Fano $V$, and $(-K_V)^n\le2n^n$ for $V\not\cong\mathbb P^n$, with equality exactly for the smooth quadric or $\mathbb P^1\times\mathbb P^{n-1}$. A boundary-pair version was not naturally posed from the source's induction (the companion input has boundary-zero scope). The source explicitly leaves the sharpness of the singular bound unaddressed (lines 78–80). No route to it was identified, and it is not a closable operation.

## 041 — Lagrangian bases

Main direction; see `route-041.md`. The nonprojective Kähler case is a paid composition and was not frozen.

## 062 — contact Fano / LeBrun–Salamon

- **Read.** Introduction.
- **Stop.** The source already covers projective contact manifolds (`thm:projective-contact`, via Demailly and KPSW) and the quaternionic-Kähler corollary.
  - For a compact Kähler contact manifold with $b_2=1$, $h^{2,0}=0$ makes it projective, so the extension is immediate (routine).
  - For $b_2\ge2$, a nonprojective Kähler analogue of the KPSW structure theorem $X\simeq\mathbb P(T^*Z)$ needs Kähler-MMP-type rational-curve input. The source does not supply this, and no closable route was found. That is a central gap, not a closable operation.
