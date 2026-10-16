# fresh-substantial-discovery-r2

Research sub-agent output for the ten-new-results campaign (2026-10-14/15). Proposal only; no acceptance is claimed. No shared files were edited and nothing was staged or committed.

## Result proposed

**Theorem A.** For all $n\ge2$, $\operatorname{cr}(K_n-e)=\frac14\lfloor\frac{n+2}2\rfloor\lfloor\frac{n-1}2\rfloor\lfloor\frac{n-3}2\rfloor\lfloor\frac{n-4}2\rfloor$ (Zheng–Lin–Yang–Cui 2007 conjecture; CHN survey Conjecture 29).
**Corollary B.** For $m\ge4$, $n\ge1$, $\operatorname{cr}(K_m\square P_n)$ equals the Zheng et al. formula (CHN Conjecture 74), via OWH Cor 5.1.

New range: odd $n\ge15$ for Theorem A, odd $m\ge13$ for Corollary B. The even case is a re-verified consequence of OWH 2014 Thm 3.2 plus upstream Harary–Hill; odd $n\le13$ follows from OWH Thm 3.1 plus upstream Harary–Hill and integrality.

Proof: `candidate.md` (odd case: new adaptation of the upstream rank/isotropy method with missing-pair test conditions, split spaces $\mathcal S_a,\mathcal S_b$, mixed isotropy, and a twisted localization detector).

## Files

* `candidate.md`: statement, full proof, validation summary, weakest-step attack, novelty limits.
* `source-contracts.md`: upstream labels with line numbers and hashes; literature locators.
* `checks/kn_minus_e_checks.py` + `.out`: exact rational checks A–J (stdlib, Python 3.14.7, about 37 s).
* `checks/kn_minus_e_modp_large.py` + `.out`: mod-$p$ rank and orthogonality checks for $13\le n\le19$ (numpy 2.5.4 in a scratch venv; about 18 min).
* `sources/upstream/`: pinned upstream copies (hash-verified).
* `sources/literature/`: survey PDFs/text and page fetches used for status and novelty.
* `sources/borsuk/`: pinned Borsuk sources read during screening (dropped candidate).
* `provenance.json`, `input-manifest.json`, `output-manifest.json`.

## Screening record (candidates dropped)

1. **Borsuk (family 156).** Upstream settles $d\ge9$; dimensions 4–8 need new constructions or full topological lower bounds. Judged out of reach; dropped.
2. **Ryser (family 162).** No tractable bridge from the pinned statement to an open neighbouring case found; dropped.
3. **Chia–Lee bipartite conjecture $\operatorname{cr}(K_{m,n}-e)$.** LP and rank-sum evidence supported a refinement of the upstream bipartite proof, but A. Sadhu's ResearchGate preprint (October 2026) proves it unconditionally with the same framework. Killed for novelty.
4. **$K_n-e$ (selected).** Literature status: open for odd $n\ge13$ before the upstream pin. After the pin, $n=13$ is routine; $n\ge15$ odd needs the new argument.

## Reproduce

```
cd checks
python3 -B kn_minus_e_checks.py            # stdlib only
<python-with-numpy> -B kn_minus_e_modp_large.py
```
