# r73 handoff: full author candidate T253M73

**Status: full frozen-scope author proof submitted for parent triage; independent gates not performed; campaign credit0.** The campaign stood at18/20 at assignment. This packet does not change that count.

For every source-admissible positive a and every finite m>=1, the proposed exact multiplier is

    H_2(A_(a,m);Z) ≅ Z ⊕ (Z/2)^(M_a+9+2[3 divides a]),
    M_a=|Norm(1-tau^(2a))|=L_a²-2(-1)^a-2.

The full scope in `scope-T253M73.md` is unchanged. `candidate.md` contains the general proof: complete corner sequence, integral translation homology with cyclic factor F_(2a), an explicit constant-fiber spectral lift of the primitive top class, a stable splitting argument, and the resolved Moore extension. `hostile-checks.md` explains why homology ranks, even torsion order, or a nonprimitive rational lift would not suffice.

The principal independent correctness question is the spectrum-level realization and constant-fiber map in Section4. There is no claimed unresolved author-side mathematical lemma, but the proof has not been independently accepted. The contribution gate is also open: several operations are classical or source-paid, and the author does not assign a substantiality rating. `reading-and-credit.md` explicitly compares them with actual predecessor proofs and closest primary operations. No replacement for r34's unresolved F_infinity target is claimed.

`checks.py` gives finite exact arithmetic diagnostics for100 parameter values and109 local corner germs. They are not a general proof. `controls.py` tests the integrity verifier on temporary fixtures, including a self-resealed false manifest; controls are not mathematical evidence.

## Verify without writing

Use the detached final manifest hash supplied in the handoff, not a hash inferred from the local sidecar:

```sh
python -B verify.py --expected-manifest-sha256 DETACHED_HASH
```

For canonical-tree and private-copy verification, additionally supply:

```sh
python -B verify.py --expected-manifest-sha256 DETACHED_HASH \
  --canonical-tree /home/mj-kang/Documents/Dev/math/openai-proof-research/sources/preprints-tree.json \
  --check-private
```

The verifier reads only. It binds the public inventory to the external hash, checks all46 pinned source blobs against the complete13223-entry canonical tree, and optionally authenticates the private source and primary bytes. The manifest and convenience sidecar are excluded from their own inventory. The private subtree is excluded from public inventory and redistribution; private-file checks cover the specifically receipted evidence, not arbitrary unlisted scratch files.

The source and primary receipts contain pinned raw URLs, exact Git blob IDs, SHA256 values, and paths. Semantic extents and failed local lookups are recorded separately. Context receipts hash external campaign records without copying them. `runtime.json` records Astra/high/serviceTier=default and zero nested agents.

Only this owned directory was written. No stage, commit, reset, PR, shared-index edit, contact, browser/UI, upload, or publication operation was performed. No formal or publication manuscript package was built. Public original prose is CC BY4.0 and original code is MIT; third-party rights and private evidence remain distinct. Parent owns independent gates, integration, and any decision about acceptance.
