# CORRECTIONS — fresh-opus-discovery-r1-corrected

This packet is a **corrected revision** of `fresh-opus-discovery-r1`. The original packet is
preserved **untouched**; nothing here modifies it. The frozen target (`TARGET.md`) is carried
over **byte-identical and unchanged** (no weakened variant).

## Provenance / superseded seal
- Superseded packet: `frontier/campaigns/2026-10-14/fresh-opus-discovery-r1/`
- Superseded external seal SHA256: `04ccf3f1320b91b6d7999098eefaf17b8c254f3735b38655ca89ef34ede41ef4`
- That hash is recorded here **for provenance only**. This corrected packet has its **own**
  seal; the externally supplied final hash for *this* packet is reported to the parent
  separately (it is **not** derived from, and does not inherit trust from, the old hash).
- Paired-tamper reproduction acknowledged: parent receipt
  `/var/tmp/opus-r1-paired-tamper-p6ykinye/receipt.json`, SHA256
  `07ef6d6b78ddb9ff90ba860b1498d252c7c1520b50b71df721ca15a5360ba453`. The old verifier passed
  rc=0 on that tampered copy (candidate.md appended **and** its hash/bytes updated **only** in
  the mutable `outputs-manifest.json`, frozen `seal.json` unchanged). The corrected verifier
  rejects exactly this case (see below).

## Proof corrections (candidate.md)
The mathematical conclusion is unchanged; the intermediate rigor is repaired.

1. **No compact-$\mu$ lemma at the unknown $p_{0.1}$.** The overlap Lemma requires a *fixed*
   compact range of $\mu$, so it cannot be applied at the a priori unknown quantile $p_{0.1}$
   (circular). Fix: the upper bound on $\mu(p_{0.1})$ is obtained by evaluating the Lemma at
   the **fixed** mean $\mu^\star=0.112$ (in a fixed compact range), where Paley–Zygmund gives
   $q>(0.112/1.112)(1-o(1))>0.1$ for large $n$; monotonicity of $q$ then yields
   $\mu(p_{0.1})\le0.112$. The lower bound $\mu(p_{0.1})\ge0.1$ is **Markov only** (no Lemma).
2. **Median located by bracketing, not by "$\mu\approx1$".** The claim "$\mu(p_{1/2})\approx1$"
   is neither established nor needed. Fix: bracket $p_{1/2}$ between the fixed-mean points
   $p(0.25)$ and $p(2)$ (where $q\le0.25$ and $q\ge0.667(1-o(1))$ respectively), and both
   $p(0.25),p(2)=p_c(1+o(1))\to\tfrac12$; hence $p_{1/2}\to\tfrac12$.
3. **Stirling error term.** $\log\binom n{t_n}=t_n\log n-t_n\log t_n+t_n+O(\log t_n+t_n^2/n)$;
   the earlier draft wrote only $O(t_n^2/n)$, omitting the Stirling $-\tfrac12\log(2\pi t_n)$
   term. The full error is $o(t_n\log n)$ and does not affect the leading asymptotics.
4. **Halved final constant.** The raw derivation gives width $\ge\frac{r!\log 8}{4c^r}
   (\log n)^{-r/(r-1)}(1-o(1))$; the factor $(1-o(1))$ does not by itself prove the bound with
   that same constant. Fix: the displayed theorem constant is halved,
   $c_r=\frac{r!\log 8}{8c^r}$, using $(1-o(1))\ge\tfrac12$ for large $n$.
5. **Overlap negative exponent via the exact identity.** The bound is regrouped as
   $-(j-\beta_j t)\log(n-t)+\beta_j t[\log\frac{ne}{t}-\log(n-t)]+O(j\log t)$ and evaluated
   with the **exact** $\log\frac{ne}{t}=\log n+1-\log t$ (and $\log(n-t)=\log n+O(t/n)$), which
   fixes the sign and magnitude; the $O(j\log t)$ remainder is absorbed since
   $j\log t=o(\log n)$. The earlier "$\log(ne/t)\le2\log n$" was insufficient by itself (it
   does not control the positive $\beta_j t\log(ne/t)$ term against $-j\log(n-t)$ with the
   correct coefficient).

## Verifier corrections (verify.py / seal.py)
The r1 verifier cross-checked the **path sets** of the mutable `outputs-manifest.json` against
`seal.json` and then **trusted the mutable manifest's hashes**. Changing `candidate.md` **and**
its hash/bytes in `outputs-manifest.json` (frozen `seal.json` unchanged) therefore bypassed the
seal. Fixed as follows.

- **Direct comparison to the frozen seal arrays.** `verify.py` recomputes every listed file's
  SHA256 and byte count and compares them **directly against the arrays inside `seal.json`**
  (the frozen anchor). It never trusts `outputs-manifest.json` / `sources-manifest.json` for
  verification; those manifests are themselves just listed, authenticated files.
- **External anchor only.** The trust anchor is the **externally supplied** `--anchor` hash,
  checked against recomputed `sha256(seal.json)`. The `seal.sha256` file stored in the packet
  is a convenience copy and is **not** counted as an independent trust anchor.
- **Whole-inventory authentication.** The verifier enumerates every file on disk under the
  packet (recursively, not following symlinks) and requires it to equal the seal's file set
  exactly: any **extra** (unlisted) file, any **missing** file, any **symlink**, and any
  **path-traversal / absolute** path entry causes rejection.
- **Source duplicate rejection.** Duplicate source paths and duplicate source git-blob ids are
  rejected.
- **Exact public membership.** The sealer `seal.py` is itself a listed, authenticated file, so
  the public membership is explicit and complete.
- **Paired-tamper control.** The controls below include the parent's exact reproduced case
  (mutate `candidate.md` **and** update only `outputs-manifest.json`); the corrected verifier
  rejects it because `candidate.md`'s recomputed hash no longer matches the frozen `seal.json`
  array.

## Status
Result remains **TECHNICAL**, **uncounted** (campaign 17/20 unchanged). No review/formal
pipeline applies. Freshness evidence remains **bounded** (registry + working-file scans); no
complete independent novelty screening is claimed, and no worldwide/new-to-literature priority
is asserted.
