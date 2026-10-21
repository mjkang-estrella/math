"""One-time own-root seal. Payload membership is independent of incoming identities."""
from pathlib import Path
import hashlib,json,runpy,datetime
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r161')
for n in ['FINAL.md','MANIFEST.json','REPORT.md']:
    if (R/n).exists():raise RuntimeError('refusing a second seal: '+n)
fr=json.loads((R/'freeze-record.json').read_text())
assert hashlib.sha256((R/fr['file']).read_bytes()).hexdigest()==fr['sha256']
ns=runpy.run_path(str(R/'tools/verify.py'),run_name='artifact_verifier_library')
inv=ns['inventory'](R)
(R/'FINAL.md').write_text('''# r161 final handoff: full author-proof nominee

**Uniform smoothing of prescribed block-type averages.** The full frozen statement is proved in the author argument, with independent correctness and substantial-contribution reviews still pending. No self-gate, acceptance or count is assigned. Campaign19/20/latestR041 remains supplied parent context.

For every fixed block size q>=3 and fixed number ell of cells, conditional averaging over uniform q-block partitions with ANY admissible prescribed type table has a uniform polynomial qth trace moment. For every K>0, removing a fixed block-indicator degree d(q,ell,K) gives operator norm at most N^-K, uniformly in rare tables, zero entries and arbitrarily unbalanced positive cell sizes. The projected average at a fixed vertex partition is one polynomial of degree at most d in all type counts. Exact constants and every quantifier are in [scope-frozen.md](scope-frozen.md); the full proof is [author-proof.md](author-proof.md).

The added operation is the q-replica empirical-type trace calculation and boundary-uniform entropy cancellation. Type counting, coordinate data processing, tree entropy, branching dimensions and compression are explicitly paid classical/source operations. The distinction offered for review is their exact compatibility with this rare-table channel, not a new entropy inequality. A concrete exponential second-moment subcase is only a diagnostic. No PSD rank robustness, quantum/other-cone complexity or Foulkes extension follows.

The author proof identifies no remaining mathematical gap at the frozen scope. This is not independent verification. Contribution remains uncertain: a stronger antecedent or a technical-only assessment is possible. Parent alone selects reviewers, integrates and counts. All old scopes and dispositions are unchanged.

All10 pinned Source126 source files and operative proofs were read and authenticated. Eight primary PDFs were acquired with explicit partial read extents; two access failures are disclosed. Actual I199/I202 scopes/proofs were followed on the representation overlap. History scans were coarse and admitted derivative aliases; displays were truncated and relevant portions recovered. No perfect isolation, exhaustive history or literature priority is claimed. See [comparison and validation](notes/03-comparison-and-validation.md) and [read/isolation limits](notes/04-reading-and-isolation-limits.md).

Exact finite author diagnostics passed46 table/size cases; six monochromatic spectral diagnostics also completed. These are not proof gates. Five selected-copy integrity controls behaved as expected. All artifacts remain within this exclusive root; no shared edits, Git operations, nested agents, browser UI, installation, publication, contacts, downstream formalization, manuscript or release work occurred.

The root is sealed once with its own MANIFEST.json and outside envelopes FINAL.md and REPORT.md. Verify using tools/verify.py and the three detached SHA256 anchors supplied in the handoff transcript. Private upstream/primary/history/render/copy material remains local under original rights. Artifact integrity does not assess mathematics.
''')
(R/'REPORT.md').write_text(f'''# Outside report envelope

Disposition: FULL AUTHOR-PROOF NOMINEE for the exact frozen block-table smoothing statement. No correctness/contribution grade, acceptance or count. Parent review remains pending.

Provenance: authorized Codex / GPT-6 Astra / high / default service tier. Source pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and operative proofs stipulated true. Complete tree13223 entries, SHA256 eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b. Frozen scope SHA256 {fr['sha256']}.

Core result and comparison: author-proof.md and scope-frozen.md. Prefreeze calculations: notes/01-source-and-feasibility.md and02-prefreeze-entropy-closure.md. Main operation: qth replica trace grouped by empirical vertex/block types, followed by a cycle average of classical tree-entropy inequalities and coordinate data processing. Explicit polynomial moment, degree threshold and N0; uniform all-table conclusion and containment polynomial. No rank/approximation/quantum/Foulkes claim.

Limits: contribution and correctness are independently unreviewed; search/history clearance is not exhaustive. Source/primary/history extents, admission mistakes, truncations, recovered portions, original Chow-Liu/Finner access failures, and the initial missing-numpy diagnostic failure are recorded in notes/03 and04. No missing lemma is knowingly deferred within the claimed author proof; this is an author assertion, not a gate.

Evidence: source126-authentication.json binds canonical paths,size,Gitblob,SHA256; primary acquisition receipts bind actual version URLs and bytes; incoming identities and selected-history identities are distinct from copied membership. Named incoming originals and tree were rechecked unchanged. Acceptance is only an excerpt identity, not a whole-journal identity.

Own exact payload: {len(inv['files'])} files and {len(inv['directories'])} subdirectories, excluding the three root envelopes FINAL.md,MANIFEST.json,REPORT.md. Payload manifest binds bytes, sizes and exact regular single-link file/directory membership; it does not bind permissions or mathematics. Verifier is read-only and requires independent detached hashes for all three envelopes. Five controls on a two-file selected copy with its OWN manifest passed their expected artifact decisions and preserved target hashes/modes/link counts/mtimes; atimes not bound. No inherited original manifest seals a reduced selection.

Seal timestamp UTC: {datetime.datetime.now(datetime.timezone.utc).isoformat()}. This envelope and FINAL/MANIFEST receive detached SHA256 anchors in the parent handoff transcript, independently calculated with sha256sum. No further payload mutation is intended after this single seal.
''')
# Envelopes are outside payload, so adding them has not changed inv.
assert ns['inventory'](R)==inv
manifest={'schema':'r161-exact-payload-v1','envelopes_outside_payload':['FINAL.md','MANIFEST.json','REPORT.md'],'scope_frozen_sha256':fr['sha256'],'limits':'Own exact membership; no incoming original manifest inherited; bytes not mathematical validity',**inv}
(R/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Sealed once:',len(inv['files']),'payload files;',len(inv['directories']),'subdirectories;3 envelopes.')
