# Arithmetic r98 handoff

PREFREEZE: no frozen target, no author proof, no nominee. No mathematical gate, contribution gate or count is assigned.

Runner: Factory Droid / claude-opus-5-5 / high. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Main direction: family 009, noninjective compatible maps of mod-$p$ Milnor $K$-theory

As the brief required, the lineation and place primaries were read before any further valuation-ring derivation.

- Carter–Vogt, PNAS 77 (1980) 3756–3757, read in full from page scans. It is an announcement for Desarguesian *planes* with no proofs. The proofs are in Mem. AMS 235, which was not obtained.
- Machala, Čas. pěst. mat. 100 (1975) 142–154, read in full. It proves that every homomorphism of projective spaces of any dimension (collinear to collinear; every line keeps three distinct image points; a non-collinear image triple) is induced by a generalized semilinear map over a total subring.
- Havlicek's survey (arXiv:1210.2053v1), read in full, for navigation. Radó 1969/1970 and Brezuleanu–Rădulescu 1984 were not obtained.

**Strongest reduction: Theorem D ($p=2$, author screen, not frozen).** Let $K$ be any field of characteristic 2 and $L$ as in source section 2. A compatible $\mathbb F_2$-linear $\theta:V_K\to V_L$ that satisfies both

- (N) every $K^2$-projective line keeps three distinct image points, and
- (T) the image contains a pair with nonzero symbol

is exactly $\theta_{O,\beta}[hu]=[\beta\bar u]$. Here $O$ is a valuation ring with 2-divisible value group, every $x\notin K^2$ has a best approximation from $K^2$, $\beta:\kappa\to L$ satisfies $\beta(\kappa\setminus\kappa^2)\cap L^2=\emptyset$, and some pair in $\beta(\kappa^\times)$ has nonzero symbol. The pair $(O,\beta)$ is unique.

The proof applies Machala's theorem through r97 Proposition A. An author lemma on uniqueness of lifts replaces `prop:projective-lift` in the pinned proof's multiplicativity gluing; this makes the Machala module a valuation ring. An elementary line analysis finishes the proof. A Hahn-series example shows that the class contains noninjective maps. Because Theorem D is "a classical place theorem plus the pinned proof", the brief's own test classifies it as TECHNICAL. It is recorded as a screen.

**Unpaid.** The remaining gap is the stratum with a *collapsing line*, a line with at most two image points. It comes from $\Gamma/2\Gamma\neq0$, from failure of best approximation, or from failure of residue separability. Example G (rank-2 Laurent field) has every $K^2$-plane mapping onto a triangle, and Lemma E shows that no plane can then have four image points. So this stratum needs the reduced-lineation theory in arbitrary dimension, glued with the group law. Carter–Vogt announce that theory for planes only, and its proofs were not read. For odd $p$, Example F ($2\cdot\mathrm{id}$) shows that compatible maps need not be lineations at all. Proposition A′ confines lines to block translates, but no odd-$p$ classification was reached. The full comparison gap is therefore not closed. Not frozen.

Other screens (194 Lech, 242, 198, 168, 116, 039, 266; 004 and 031 history only) are in `packet/public/screens.md`.

Novelty: nothing here is claimed new to the literature. No literature search for Theorem D's exact statement was performed.

## Inventory

- 4 retained pinned 009 source files, all read in full and blob-checked against the complete preprints tree. 17 further fetched files were removed before sealing; each removal is recorded with blob, size, SHA256, read extent and reason.
- 4 primary files: two PNAS page images, the Machala PDF and the Havlicek PDF. Exact retrieval URLs were not retained; identifiers and hashes are in `primary-register.json`.
- 7 unchanged history copies: both briefs, r97 `REPORT.md`, public report, screens, reading limits and parent intake.
- Read limits and provenance gaps, including two `/tmp` incidents, are listed in `packet/public/reading-limits.md`.

## Seal

`FINAL.json` binds this outside report, the manifest, the verifier, the controls script and the public report. Take its detached hash from the parent handoff. Run the read-only verifier and the copied controls as described in `packet/public/reproduction.md`. `integrity-results.json` is written outside the packet and must be hashed separately. Author notes and scratch under `work/` are outside the packet and unsealed. These artifact checks are not mathematical gates.
