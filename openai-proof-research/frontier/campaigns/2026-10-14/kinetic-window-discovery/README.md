# I340 kinetic window discovery (2026-10-14)

**Verdict: candidate full theorem, pending an independent proof gate. Not yet countable.**

**Target.** The unsmoothed path-space fluctuation theorem for H, the pinned
`Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026` at `fd4aeeb2…`:

- the actual deterministic hard-sphere gas;
- grand-canonical excluded product activity on ℝ³×ℝ³, including N=0, with μ=ε⁻²;
- H's f₀ hypotheses, on the **supplied** regular interval [0,T];
- exact microscopic centring at every t;
- a finite vector of C_c^∞ tests;
- convergence in D([0,T],ℝ^m), J1, to the continuous Gaussian coordinate modification.

**Result.** Theorem K (`analysis.md` §1) states exactly this target. It is proved in
`analysis.md` §§3–7 from H's stipulated statements and the prior I340 transfer and continuity
lemmas.

**The new bridge (Lemma A).** H's chronological merger chart has a measure-preserving
time-translation flow: shift every merger time by λ and shear the initial-link vectors by −λΔv.
Every contact time moves along this flow at unit speed. That includes a *redundant* contact, whose
time is a determined function of the merger parameters, so it has no coordinate of its own.

Averaging over the flow turns the event {t_r∈W} into the factor |W|/Λ. The cost is a domain sweep:
a factor e(1+a)/τ in time volume, plus one 1/ε, paid by a physical link's ε gain. H's μ^{1−h} root
gain, fresh-label factorials, restarts and summable base Cτ√L are unchanged.

**What follows from Lemma A.**

- **Prop. B:** E|ΔX̂|⁴ ≤ C(δ²+δ/μ)+Cμ²ε^P. The qualitative rᵋ is gone.
- **Prop. C:** a microscopic modulus at α=μ⁻⁷ᐟ³, from EZ_W³ ≤ C(μα+μ³ε^P), where Z_W counts the
  particles that collide in a cell.
- **GRR on the grid interpolation**, then transfer to the true gas.

**Points a referee must check** (`analysis.md` §9):

- **R1:** collision-flag records. This is the only non-literal extension of H, and it is used only
  in Prop. C.
- **R2:** H's chart applied to affinely extended histories inside an upper bound.
- **R3:** uniformity in pulse and window positions.
- **R4:** the order of averaging and pair summation.
- **R5:** measurability.

If R1 fails, `objections.md` §D gives the smallest unpaid operation.

## Files

| File | Content |
|---|---|
| `analysis.md` | statement, Lemma A, Cor. A′, Prop. B, Lemma R, Prop. C, Lemma G, proof of Theorem K, risks |
| `objections.md` | disposition of every prior objection; prior gaps carried forward explicitly |
| `reading-and-sources.md` | primary-source reading and hash map; BGSS comparison; bounded literature check; credit |
| `input-authentication.json` | full hashes, git blobs, read scopes, restrictions, deduction status |
| `checks/` | `shift_covariance.py`, `exponents.py`, `toy_window_density.py`, `verify_sources.py`, and `OUTPUT.txt` (all PASS; numerics are illustrations) |

Run `python3 -I checks/<script>.py`. For `verify_sources.py`, pass `../../../../sources/preprints-tree.json`
from this directory to also compare blob ids.

**Restrictions observed.**

- No agents, no git, no publication.
- No shared index or prior artifact was modified.
- Writes are only in this directory.
- The pinned source copies fetched for reading were deleted.

**Novelty.** A bounded search found no long-time nonequilibrium process theorem for hard spheres.
That is not a novelty proof, and no priority is claimed for the elementary time-translation
mechanism itself.
