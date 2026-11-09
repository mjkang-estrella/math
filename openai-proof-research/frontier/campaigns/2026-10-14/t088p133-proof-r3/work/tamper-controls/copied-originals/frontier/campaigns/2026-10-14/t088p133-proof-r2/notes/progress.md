# T088P133 correctness review round2 - durable progress notes

Reviewer root: frontier/campaigns/2026-10-14/t088p133-proof-r2/ (exclusive writable).
Round1: provider/network failure, no verdict, no authored objection found in failure records; r1 root preserved
read-only (5 partial files per proof-r1-partial-snapshot.json). Round2 evaluates independently from scratch.

## Start bindings (work/input-hashes-start.txt)
- AGENTS.md e9ab9518... (matches r1 start binding)
- research-brief-2026-10-20.txt e97190d3... (matches r1)
- proof-r1-brief.txt 0ba65bd8... (matches r1)
- proof-r2-brief.txt 68643c0b... (new, round2 routing overlay)
- proof-r1-failure.json e406efb7..., proof-r1-partial-snapshot.json 84e95141...
- sources/upstream.json 3784eb61... (pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb)
- sources/preprints-tree.json eeecc1da... (13223 entries, truncated false; matches brief)

## Author authentication (work/author-hashes-measured.txt)
All detached anchors reproduce exactly:
- FROZEN-THEOREM.md 86e1f30e...d354 (= scope anchor in brief)
- proof.md 971506a4...bc84 (= proof anchor)
- FINAL.json 4656a93d...cd09, MANIFEST.json 9ab6adfb...6324, REPORT.md 3659f82e...49fd
- certificate.py 560f9813..., geometry_control.py e14d51f3..., controls.py f07c8e39..., verify.py ae5bb2e7...,
  reading-limits.md 1753bcbc..., report.md 4269dd1e... all match MANIFEST.json entries.

## Independent acquisitions (downloads/)
- sourceP/{README.md,main.tex,references.tex} from pinned raw GitHub URLs at fd4aeeb2...;
  git blob SHA-1 all MATCH preprints-tree.json (b46aac76..., c3218753..., b5ca002e...);
  sha256 equal to author packet/private copies (independent fetch, same bytes).
- fhlx-2610.13953v1.pdf sha256 4a9c5193...bf25 (identical to r1's unsealed partial download; r1 failed at reading it).
- fhlx-2610.13953v1-eprint.tar sha256 178708f3...9559, contains single toplevel ______-2026.8.26.tex
  (sha256 bbadc44d...da49, 1705 lines), pdflatex/texlive2025 per 00README.json.

## Exclusions honored
Not reading: fresh-arithmetic-discovery-r100/, t165p135-contribution-r1/, t088p133-contribution-r1/,
parent contribution-disposition.md and contribution-r1-adoption/. No git/shared-index mutations.

## Audit log (to be filled as derived)
