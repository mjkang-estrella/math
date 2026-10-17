# AGM063 manuscript implementation

Final manuscript implementation for independent manuscript review. The full
five-type classification remains a human proof conditional on stipulated S1
and essential S2 and the stated classical inputs. No final acceptance, worldwide
priority, external peer review, campaign count change, or full geometric
formalization is claimed.

The manuscript is `output/pdf/advanced-mukai-classification.pdf` (nine pages).
`main.tex` contains the mathematics and bibliography; `formal-support.tex` gives
precise audited support coverage. `formal-coverage.json` records the implementation
and independent formal-review anchors. That review returned PASS_SCOPED_SUPPORT
and was adopted by the root; it concerns 29 abstract supporting theorems across
35 public declarations, not the geometric classification.

The mathematical draft and Watanabe primary comparison were prepared by the
original candidate author. `reading-limits.md` is that author's historical
reading record. A successor implementation worker continued the draft; its own
reads and work are recorded separately in `finalization-reading-limits.md`.
`private/original-draft/` preserves the prior checkpoint's exact named payloads.
`draft-checkpoint.json`, `continuation-checkpoint.json`, and
`formal-coverage-draft.md` are historical checkpoints, superseded by
`final-checkpoint.json`. They do not describe the current artifact status.

The original proof/contribution reviews and all source packages remain immutable.
The independently requested pre-seal genus-zero precision edit to Lemma 2.1 is
recorded in the final reading addendum. All R1-R4 and optional editorial responses
are mapped in `source-map.md`; the full five-type theorem is unchanged.

## Verification

Obtain the final manifest SHA-256 from the parent or another external trusted
receipt, then run from this package:

```sh
python3 -B verify.py --anchor EXTERNALLY_SUPPLIED_SHA256
```

The verifier is read-only. It authenticates the manifest against that external
anchor, checks exact files and directories, refuses symlinks, hard links and
nonregular files, checks every size/hash, and binds the final sources, PDF,
rendered pages and recorded formal adoption. No files or control logs are exempt
except the manifest itself, which is authenticated by the external anchor.
The verifier does not prove the mathematics or perform visual inspection.
`checks/integrity-controls.json` records real isolated tamper controls and
restoration; the altered copies were removed. A digest computed solely from an
untrusted package is not an external trust anchor.

## Rebuild

Copy the package before rebuilding: this overwrites generated outputs and
invalidates the old seal and visual-review record. Use Python 3, Tectonic 0.17.0,
and Poppler. The actual final build used:

```sh
python3 -B build.py --tectonic /tmp/frontier-typeset/tectonic
```

Supply the equivalent installed compiler path on another machine. The default
uses cached Tectonic resources; `--allow-network` can populate a new cache. The
build fixes SOURCE_DATE_EPOCH, records compiler and source hashes, renders every
page and rejects overfull boxes, undefined references and unresolved rerun
warnings. `checks/visual-review.json` records direct inspection of every final
page, bound to the exact PDF and page PNG digests. A rebuild requires a new
all-page inspection; it cannot inherit that assertion automatically.

`python3 -B integrity_controls.py --final-ready` and `python3 -B seal.py` were
run before sealing. They are authoring tools, not read-only verification tools;
they refuse to run over an existing seal. The final manifest is the last package
write. Retain its printed digest externally.

Private inputs and third-party bodies are for review provenance only and must
be excluded from any eventual public selection. No upload occurred. Myeongjin
Kang is the author, with no affiliation. Original prose is CC BY 4.0; original
code is MIT. Third-party licenses remain their owners'.
