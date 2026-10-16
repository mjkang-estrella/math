# Unchanged sextic Salem T, round 2

**UNRESOLVED; campaign 4/10.** Read candidate.md for the exact unchanged
scope, audit, conditional estimates, construction attempts and unpaid gap.
No manuscript, Lean or independent proof/contribution gate is claimed.

Author Myeongjin Kang, no affiliation. Original prose CC BY 4.0/code MIT;
third-party inputs private, with retained rights and provenance.

Verification uses an externally supplied detached SHA256 of seal.json:

    python -B verify.py --anchor <external-terminal-seal> --exact

Without --exact it performs only read-only authentication. Wrong anchors,
wrong required mathematical status, hash failures or extra/missing members
stop BEFORE the exact checker can be loaded. The exact option runs only the
rational checker for one unsuccessful unit element after authentication,
under an audit hook denying writes/network/subprocesses. Discovery scripts
are not imported by the verifier. The checker does not establish T.

The two discovery scripts write JSON only to stdout. unit_probe.py uses
Decimal embeddings and reduced floating cosines. lattice_probe.py imports
that inspected local module and adds Decimal LLL selection with exact integer
transforms. Neither is an interval certificate; their fixed search extents
are recorded in candidate.md and saved evidence. No old script was executed.
The exact checker uses integer quotient arithmetic and outward rational
intervals with analytic infinite-tail bounds.

The exact sealed r11 package is externally referenced rather than recopied.
Mutable ledger, rules and parent context have local immutable snapshots.
verify.py never overwrites a fixture or source. Receipt checks authenticate
bytes and finite arithmetic only, and do not award an independent PASS.
