# Validation performed and its exact limits

Pre-seal author checks:

* Recomputed SHA256, byte count and Git blob identity of all 33 canonical
  pinned source files; the pin is unchanged.
* Recomputed SHA256 and byte count of all 10 retained primary files (five
  PDFs and five extracted-text files). This verifies identity, not a full
  reading of their contents. reading-limits.md records actual body ranges.
* Recomputed every copied coauthor-note hash against its recorded snapshot
  receipt. These are author contributions, never independent reviews.
* Parsed all three Python scripts and replayed interface-checker.py; output
  exactly equals interface-checks.json, with seven finite groups/cases.
* Checked that all 13 Markdown proof-module references in candidate-proof.md
  resolve locally. dependency-map.md gives their logical ordering.

The final external validation receipt will contain the actual manifest anchor,
identity verifier output, and all eleven reason-checked identity control
outcomes. Those controls include a positive copy, wrong anchor, changed,
missing and extra payloads, extra directory, altered manifest, symlink payload,
hardlink, FIFO and root symlink. They run only in disposable /var/tmp copies.
The receipt is external to avoid a self-referential manifest hash.

Neither identity controls nor finite arithmetic checks verify the theorem.
No formal proof, numerical approximation of infinite paths, independent proof
review or contribution review is represented by these outputs. The full
result remains an author proof claim pending those independent campaign gates.
No source/private PDF or extracted body is selected for publication; this is
an internal research packet with ignored private evidence and no upload.
