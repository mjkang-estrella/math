"""One production seal of this exclusive review root; no source mutation."""
from pathlib import Path
import datetime,json
ROOT=Path('frontier/campaigns/2026-10-14/structural-r161-contribution-r1')
for name in ('FINAL.md','MANIFEST.json','REPORT.md'):
    if (ROOT/name).exists():raise RuntimeError('Production envelope already exists: refuse reseal')
ns={'__name__':'seal_inventory'}
exec(compile((ROOT/'tools/verify.py').read_text(),str(ROOT/'tools/verify.py'),'exec'),ns)
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
(ROOT/'FINAL.md').write_text('''# T126S161 contribution review

**TECHNICAL, conditional on correctness, for the entire unchanged frozen scope.** No correctness verdict, acceptance, campaign count or priority claim is made. Parent alone integrates.

The decisive complete classical composition is in [review.md](review.md). Finite type-class estimates, applied to block compositions and vertex colorings, give the normalized pair kernel at every admissible table. Coordinate data processing and the average of the q spanning-path tree-projection identities yield

    tr((T_t^*T_t)^q) <= (N+1)^(C-1-3q) <= exp(C)(N+1)^C.

This pays the entire proposed boundary-uniform replica normalization/cancellation, including rare events and zero entries. Source126's compatible stabilizer/tableau/compression argument then gives exactly the frozen d and N0; its containment count gives the single polynomial simultaneously across all tables for every d>=0 and arbitrary real f. No full-scope restriction or renaming is made.

Scope SHA256: b5c7b51d352e250df511fae5d3456ccbaa2756180111020b3108415c12a7d813. Author-proof SHA256: f522cf05688e557aa7934946ee79564ee55238f0057423135a58c4d9abee451a. Supplied author envelope anchors matched; tracked input bytes/modes remain unchanged.

[Reading/isolation record](notes/02-reading-and-isolation.md) gives exact actual proof extents, incidental tails, truncation recovery, bounded searches and the original Chow-Liu1968 HTTP403 failure. The accessible2020 primary proof was read. No general title-identical antecedent or exhaustive history/literature search is claimed. Two search receipts were briefly written above the project and immediately relocated into this root; the empty erroneous directories were removed, and no source/shared file was altered. This corrected write-boundary violation is disclosed, not described as perfect isolation.

The read-only verifier checks this exact selected payload and all three detached envelopes. Seven small copied-control outcomes matched expectation. These are integrity checks only. Original review/code and private source/primary/history/frozen/search/render material are separated; original rights remain, and no original whole-manifest seals a reduced copy. Detached FINAL/MANIFEST/REPORT SHA256 anchors accompany the parent handoff.
''')
inv=ns['inventory'](ROOT)
manifest={'schema':ns['SCHEMA'],'sealed_at_utc':now,'scope_sha256':'b5c7b51d352e250df511fae5d3456ccbaa2756180111020b3108415c12a7d813','envelopes_excluded':['FINAL.md','MANIFEST.json','REPORT.md'],**inv}
(ROOT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
(ROOT/'REPORT.md').write_text(f'''# Outside integrity and review report

Disposition: TECHNICAL conditional contribution, ENTIRE unchanged T126S161 frozen scope; no correctness decision, acceptance, campaign count, worldwide-priority assertion or downstream action.

Mathematical payment: review.md derives the stronger all-table qth trace bound with E=C-1-3q using literal finite type-class bounds, exact incidence normalization, data processing and tree-projection KL identities. It carries through the precise frozen norm constants and simultaneous polynomial for arbitrary real f and all admissible tables. No incompatible dense-table or multiplicity-free premise is used.

Operative evidence: pinned Source126 complete matching-smoothing appendix; Csiszar SectionII proofs with rendered formulas; Bhattacharyya et al2020 tree-projection proof; primary Gowers and Vershik-Okounkov representation arguments; Filmus-Lindzey and Meagher et al actual general hypermatching proof portions. I199/I202 originals followed without modifying their targets/dispositions. Read extents and limits are in notes/02-reading-and-isolation.md. Original Chow-Liu1968 retrieval failed HTTP403; no exhaustive search/priority claim.

Provenance and preservation: direct AGENTS/upstream read. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and operative sources stipulated true. Complete preprints tree13223 entries, SHA256 eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b. Frozen scope/proof and all three detached author envelope hashes matched. End checks preserve tracked original bytes/modes and selected fixture mtimes; atimes and whole-author-tree stability are not certified.

Independence: prospective excluded full paths recorded before traversal. No correctness-review/sibling body or peer status read, no author contact, no agents, Git, shared edits, browser UI, heavy installation, publication or formal/manuscript work. Actual corrected exception: two own search receipts briefly landed one directory above the project via relative apply_patch; moved to this exclusive root and only empty mistakenly created directories removed. Not perfect write isolation. No original/source/shared file affected.

Own production payload: {len(inv['files'])} regular single-link files and {len(inv['directories'])} subdirectories, with exact membership, bytes, sizes and permission modes bound. The three root FINAL.md/MANIFEST.json/REPORT.md envelopes are outside that payload and require independent detached SHA256 anchors. No incoming whole-original manifest is inherited. Private selected source/primary/history/frozen/render/search material stays under original rights, distinct from original review and code.

Seven bounded selected-copy controls: baseline, changed bytes, missing/unexpected member, extra member, changed mode, wrong detached anchor, and restored baseline all produced expected outcomes; source review/verifier bytes/modes/link counts/mtimes unchanged. Integrity is not a mathematical gate. tools/verify.py is read-only.

One production seal at {now}. No further payload mutation intended. Independent sha256sum anchors and an anchored read-only verification follow in the handoff transcript.
''')
print('Production seal written once:',len(inv['files']),'payload files,',len(inv['directories']),'subdirectories.')
