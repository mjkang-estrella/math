# Local draft archive assembly

Run from the `openai-proof-research` root:

```sh
python3 frontier/campaigns/2026-10-14/p-gradient-release/assemble.py /tmp/p-gradient-draft.zip
```

The output path must not already exist. The assembler captures the selected
source bytes, checks the manuscript and formal validation hashes, checks
all four original proof-review inputs, and rejects concurrent input changes.
It writes an explicit draft label, a SHA256 manifest, reproducibility
instructions, and a ZIP containing the manuscript, formal sources/pins and
relevant authored reviews. It reads no credentials and makes no network calls
or submissions. Third-party papers and dependency caches are not bundled.
Original paths are retained so the Lean project and most research links work
on extraction; links to excluded source scans remain external references.

The first assembly at context commit `4f302a5a` succeeded with 50 project
files. Its disposable `/tmp/frontier-typeset/p-gradient-draft-check-1.zip`
had SHA256 `cab52943d11cbc1d9a20c1f3399739f73a6679d5dd8a3a728ba01917f337f509`.
The parent extracted it to a new temporary directory, checked every file's
length and SHA256 against its manifest, and ran both round-1 and round-2
review scripts there; both exited 0. This demonstrates archive integrity
and script portability, not the analytic theorem or a clean-machine Lean
build. The previous Lean build/axiom audit remains separately recorded.

This temporary archive precedes the active manuscript consolidation and
must be regenerated after the final manuscript gate. The assembler always
labels its output DRAFT; it cannot declare acceptance or publication.
Author names, affiliations, license and external identifiers remain unset.
