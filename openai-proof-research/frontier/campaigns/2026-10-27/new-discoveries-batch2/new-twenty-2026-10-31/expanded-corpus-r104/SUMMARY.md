# expanded-corpus-r104: summary

**Lane:** expanded-corpus-r104 (reserve5 selection, 20 IDs). Single investigator (Claude Opus 5.5), no child agents, no git, no shared-ledger edits. The accepted count is not changed; credit is zero unless root accepts.

## Headline candidate: 358158, refuted at m = 5 with a full Lean endpoint

The conjecture is Conjecture 1 of Chu–Wang–Zhang (arXiv:2304.11403v1): for odd m, the generating set of all TC-dominant length-m words gives m-SSA codes of the largest rate. The source verified this by brute force at m = 3 only.

**Counterexample (m = 5).** Take the TC-dominant set and swap 22 weight-3 words for their reverse complements:

`AACCC CAACC CAACT CAATC CAATT CAGCC CAGCT CCAAC CCAAT CCAGC CCCAA CCGAC CGACC CGACT CTAAC TAACC TAACT TCAAC TCAAT TCAGC TCGAC TTAAC`

The result is a generating set in S_5 with spectral radius 3.2480375901. TC-dominance gives 3.2443334586, which corresponds to the source's 1.6980 bits/nt. The new rate is 1.699591 bits/nt.

**Proof.**

- Integer Collatz–Wielandt certificates give |C_n(S5)| ≥ c1 (1299/400)^n and |C_n(TC)| ≤ c2 (649/200)^n.
- A transfer identity, proved from the literal window definition of C_n(S), turns the certificates into these bounds.
- The rates then differ by at least log2(3.2475/3.245) asymptotically.

**Lean** (`formal/SSA5/`).

- The definitions are literal: Definitions 1–5, TC-dominance as "more than m/2", and rate = (1/n) log2 |C_n(S)|.
- The endpoints refute the conjecture in its limsup and liminf readings. They also show that rate(S5) ≥ rate(TC) + ε whenever both limits exist, and that an eventual uniform gap holds. Both sets are proved to be generating sets.
- Fresh extracted strict rebuild (`-DwarningAsError=true`) passed for all 7 modules. `leanchecker` passed on all 7.
- The audit covered 198 declarations, including generated ones. The only axioms are propext, Classical.choice and Quot.sound. There is no sorry, admit, native_decide or ofReduceBool.
- Finite facts are checked by `decide +kernel` in about 4 s. Peak RSS is about 2.8 GiB.

**Open points for root.**

1. The journal version's body is unread: Wang–Chu–Ge–Zhang, IEEE T-MBMC 2024, document 10517954. IEEE returned 202 with an empty body, which I did not retry. Its abstract reports optimal rates only for m = 2 and 3.
2. Significance: the rate gain is small (0.00167 bits/nt), the source is a cs.IT preprint, and only m = 5 is refuted. Capped m = 7 searches did not beat TC.

Full write-up: `SSA5-REFUTATION.md`.

## Other dispositions (`results.json`, 20 entries)

**Known or excluded:**

- **376109:** proved in its own source (Kaul–Mudrock–Straub 2026), giving P_l^u = P^u = C(k+n−1, n).
- **382507:** disproved in its own source (Bérczi et al. 2026).
- **355626:** the source states that HRS Conjecture 6.2 was proved by Ferroni–Matherne–Stevens–Vecchi (Corollary 3.17).
- **353210:** the source proves Conjecture 1 (OEIS A187660) in Section 4.

**Proof found but likely routine (not formalized):**

- **356309:** the identity depends only on N = ℓ + 2g. A one-step Lagrange inversion (x = t(1+x)², t = y/4) proves it for all N ≥ 2. Exact checks over 7,200 cases agree.

**Extended searches with no counterexample (parked):**

- **367930** (CA prefix sums):
  - Exhaustive for one-sided radius r ≤ 4. At r = 4 all 601,080,390 balanced rules were covered, and no surjective rule violates the conjecture.
  - A structured sample of 20.4M permutive and composed rules with radius 5–12 found no violation.
- **366890** (Bressoud companions):
  - Exact equality for k = 5–7 with n ≤ 8, and for k = 5 with n ≤ 15.
  - Controls pass: the proven cases k ≤ 4 agree, and a perturbed variant fails.
- **372943 / 368570** (same Chen et al. conjecture, W = 7, bound 13):
  - 70,084 random maximal graphs with W ≤ 7 reach a maximum strong chromatic index of exactly 13 and never 14.
  - The bound values come from C5 blow-ups.

**Parked without computation:**

- **368815:** transfer-system complexity.
- **368968:** Speyer's N_2 twist invariance.
- **353595:** Theta conjecture; needs a symmetric-function CAS, which is not available here.
- **355004:** zircons in types D and E.
- **340290:** parabolic F-triangle. A route via the core label order of Tam(α) is identified but not implemented. The MathDB F-from-H definition also needs a fidelity check against the source's M-based definition.

**Source-backed dispositions only** (analytic, asymptotic, probabilistic or set-theoretic): 343294, 373174, 372830, 373663, 361056.

## Registries and access

- **OpenAI/math:** HEAD 4eaee875, unchanged.
- **Omega:** HEAD is now 3e6639b6 (2026-11-02T06:22Z), newer than the root-known a9de93a5. I fetched complete, untruncated D5 (13,434 entries), Problems (1,646) and OpenAI preprints (13,578) trees. These are path screens only.
  - There are no SSA, DNA or secondary-structure hits.
  - The Chapoton and Speyer hits are unrelated: Chapoton–Han arXiv:2001.01449, and the uniform-matroid g-polynomial.
- **arXiv:** abs and pdf only (no API). 2304.11403 has v1 only.
- **IEEE:** the 202 challenge was not retried.

## Resources

- Every run went through `scripts/limited.py`, or `scripts/limited_lean.py` for Lean, which allows 64 GiB address space. Each run used 2 CPUs, 120 s CPU, 140 s wall and a sampled 6 GiB RSS cap, with logs and receipts in `logs/`.
- The largest Lean RSS was about 2.9 GiB. Full `import Mathlib` hit the RSS cap once (killed at 6.4 GiB), so the packet uses targeted imports.
- One Python count run hit the CPU cap and was rerun with a smaller range.
- No background jobs are left running.

## Files

- `results.json`: the 20 entries.
- `extracted.json` and `raw/`: exact corpus lines with chunk, line and hashes.
- `history-matches.txt`: the prior-note screen. It found only the reservation ledger and hash-substring noise.
- `sources/`: PDFs, text, receipts and registry trees.
- `scripts/`: `ssa/`, `ca/`, `sci/`, `misc/`, `lean.py`, `checker.py` and `registries.py`.
- `outputs/`: `ssa5-best-set.txt`, `ssa5-certificate.json` and `ssa5-structure.json`.
- `formal/SSA5/`: the working packet.
- `replay/`: the fresh extracted rebuild, with `source-sha256.txt`.
- `MANIFEST.json`.

## Disclosure: a file outside the lane

The JVM ignores TMPDIR and created an empty directory, `/tmp/hsperfdata_mj-kang`, at the first `java` run (2026-11-02 07:07 UTC). Its per-process files are deleted when the JVM exits. I removed the empty directory with `rmdir` at handback. Future Java runs should pass `-XX:-UsePerfData -Djava.io.tmpdir=<lane>/tmp` to avoid this. No other file outside the lane was created: Python bytecode writing was disabled, and Lean builds wrote only to `formal/build` and `replay/build`.
