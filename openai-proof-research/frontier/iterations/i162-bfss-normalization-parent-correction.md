# S155 normalization correction and parent disposition

**Original exact-reduction claim: FAIL. Corrected leading-law deduction:
supported by I162's independent analytic review. Contribution: still open.**
This is a separate correction, not an edit or retrospective PASS of S155.
Eight findings remain accepted; two remain.

## 1. Source mismatch and exact replacement

The parent read the complete [I162 review](../reviews/i162-fixed-sector-bfss-focused-astra.md)
and directly checked the pinned TeX's Lemma `lem:form`,
equations `eq:form` and `eq:potential`, lines 236–256, and its proof ending
at lines 310–324. The
[immutable upstream TeX](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Positive-eigenvalues-of-the-relative-SU-2-BFSS-Hamiltonian-October-5-2026/build/positive-eigenvalues-relative-su2-bfss.tex)
has SHA-256
`c6d02247561556ab27c8015579045a8a71f20214261a14c810175979970621ce`.

With exactly its Clifford, structure-constant and summation conventions,

$$
B_{\rm src}(X)=\frac{i}{2}\sum_{i,a,b,c,\alpha,\beta}
f_{abc}x_i^a\gamma^i_{\alpha\beta}
\theta_\alpha^b\theta_\beta^c,\qquad
f_{abc}=\sqrt2\,\varepsilon_{abc}.
$$

Original [S155](i155-fixed-sector-bfss-counting.md), line 141, instead writes
$2i$ in the diagonal formula. The parent checked that line and the
associated coefficient calculation at line 83. The asserted exact matrix
is four times the source matrix. The source's unambiguous TeX controls;
linearized PDF fraction order does not justify the replacement.

For the corrected candidate, replace that diagonal formula by

$$
B_{\rm src}(D_s)=\frac{i}{2}
\sum_{a,b,c,\alpha,\beta}f_{abc}s_a\gamma^a_{\alpha\beta}
\theta_\alpha^b\theta_\beta^c.
$$

Every occurrence of $B$ in the corrected exact reduced form and subsequent
proof means this source matrix. The operator remains the **original
closed physical supercharge form**. We do not define a Hamiltonian with
fourfold fermion coupling and transfer the source confinement theorem to it.
I162 §2 additionally supplies an actual-sector nonvanishing argument;
the parent does not substitute finite checks for that argument.

## 2. What survives and why

The upper bound $C=1024$ remains valid. Using
$\|\theta_\alpha^a\|=1/\sqrt2$, the entrywise gamma bound $64$, and the two
nonzero color orders, the corrected calculation gives

$$
\|B_{\rm src}(X)\|
\le32\sqrt2\sum_{i,a}|x_i^a|
\le96\sqrt6\,|X|<1024|X|.
$$

Thus the earlier larger estimate was a valid overestimate, although its
asserted exact coefficient was wrong. We keep $m=3072$, $M=6$,
$c_m=(m+9)/3-1024=3$, and
$\lambda=(3086,3080,0,0)$ with $\lambda_2>m+M$.
No representation or threshold is weakened to repair the proof.

The stipulated sector confinement inequality applies directly to
$B_{\rm src}$ on the original form. Its convex combination with the
source gradient-plus-quartic inequality supplies the same positive
gradient, quartic and radius control. After scaling by $E^{1/4}$ and
dividing energy by $E$, the fermionic matrix contributes
$h B_{\rm src}(D_t)$, $h=E^{-3/4}$. It is lower order on every fixed
compact regular chamber. The weighted cell bounds control the excluded
collars and horns before those cutoffs are removed. I162 §§3–8 give the
full corrected representation, domain, localization, counting and
phase-integral argument, rather than assuming that changing any
lower-order term preserves a noncompact Weyl law.

Accordingly the corrected candidate retains precisely

$$
N_\lambda(E)\sim d_\lambda m_\lambda
\frac{\sqrt2\,\Gamma(1/4)^2}{270\pi^{3/2}}\,E^{9/4},
\qquad
m_\lambda=\dim\operatorname{Hom}(V_\lambda,F)^K,
$$

for each fixed source-constructed confined physical type in S155's scope.
The full stabilizer, its central lifts, full isotypic multiplicity and
inherited physical domain remain as specified and reviewed. The displayed
explicit type has $m_\lambda>0$. This is not a full-Hamiltonian law,
uniform-in-type estimate, massless gap, or statement about sector mixing.

## 3. Verdict and evidence history

- S155's unchanged exact matrix/form assertion fails. Its other separately
  scoped PASS verdicts are those listed by I162, not a blanket original PASS.
- I158 remains incomplete and unsealed. Its narrower no-repair PASS missed
  the coefficient error and is not adopted.
- The parent explicitly adopts the correction above for the candidate sent
  to the contribution gate. I162 supports the corrected leading-law proof;
  neither the correction nor that proof is a substantiality decision.
- Original S155, I158, their task records and evidence remain byte-identical.
  The correction is not written into an old sealed artifact.

I158's exact baselined preparation and report are archived with this
checkpoint as **incomplete historical evidence**, so I162's preservation
checks retain their inputs. Its old scripts are not executed and its
prevalidation is not repaired or resealed.

The [parent replay](../experiments/i162-parent-verification.json) passed:
26 owned files, 51 immutable references, 35 preserved ancestor files,
three pinned blobs, 455 finite metric cases and seven guard tests.
The reviewed seal has SHA-256
`1da3611744b48f35763cb7d16f30fb3ce8e6c05e5f136e9ba07a50a71c0f7448`.
The verifier performs byte checks before its finite diagnostics and executes
no ancestor program. These results verify evidence and finite arithmetic,
not the universal proof or novelty.

The separate contribution review must assess the **corrected entire
theorem**, including noncompact horns and singular strata, against the
strongest source operations and primary literature. The original failure
must remain visible whatever that review concludes. No finding is accepted
by this checkpoint.

[I163](iteration163-corrected-bfss-contribution-factory-astra-task.json)
is the fresh Factory/Astra contribution round. It must first confirm the
correction and keep any new proof objection separate from substantiality.
