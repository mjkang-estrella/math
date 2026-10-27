#!/usr/bin/env python3
"""Assemble only the independently hashed peakon payload; preserve originals."""
from pathlib import Path
import hashlib
import json
import shutil

LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[1]
DEST = ROOT / 'candidates/peakon-coefficients'
REVIEW = ROOT / 'lanes/pi-peakon-final-review'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    frozen = json.loads((LANE / 'final-review-hashes.json').read_text())
    assert len(frozen) == 64
    assert not DEST.exists()
    for name, digest in frozen.items():
        assert sha(LANE / name) == digest, name
        target = DEST / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(LANE / name, target)
    locations = {name: name for name in frozen}
    for name in ['main.tex', 'paper.pdf', 'paper-qa.json']:
        original = DEST / 'reviewed-originals' / name
        original.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(DEST / name, original)
        locations[name] = str(original.relative_to(DEST))
    (DEST / 'reviewed-parent-hashes.json').write_text(json.dumps(frozen, indent=2) + '\n')
    (DEST / 'reviewed-file-locations.json').write_text(json.dumps(locations, indent=2) + '\n')
    for name in ['review.md', 'provenance.json', 'evidence/independent_check.py']:
        target = DEST / 'reviews/final' / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(REVIEW / name, target)
    audit = REVIEW / 'candidate-copy/build/verified/audit.json'
    assert audit.read_bytes() == (LANE / 'verification/full121-audit.json').read_bytes()
    shutil.copyfile(audit, DEST / 'verification/independent-audit.json')
    shutil.copyfile(LANE / 'verification/full121-audit.json', DEST / 'verification/parent-audit.json')
    source = (DEST / 'main.tex').read_text()
    old = 'Complete final formal, manuscript and wider novelty review is pending; no priority claim or discovery credit is made here.'
    new = 'Independent final source, mathematical, formal, manuscript and bounded novelty review has passed. No worldwide priority claim is made.'
    assert old in source
    source = source.replace(old, new)
    old = 'its identity $T_{ii}=p_i$, eq.~(5.6),'
    new = 'its identity $T_{ii}=p_i$, from eqs.~(2.2) and (5.6),'
    assert old in source
    source = source.replace(old, new)
    old = 'Independent final formal/manuscript review is pending. Discovery credit remains zero; no global priority or optimality claim is made.'
    new = 'Independent final review passes all five gates. Discovery acceptance additionally requires a fresh replay from the extracted proof packet; no global priority or optimality claim is made.'
    assert old in source
    (DEST / 'main.tex').write_text(source.replace(old, new))
    (DEST / 'reviews/parent-final-addendum.md').write_text('''# Parent reconciliation of the final independent review

All five gates PASS on the 64-path freeze at 41bea8af21b2005dde02a3ff57b578141267d875.
All 64 reviewed originals are preserved by reviewed-parent-hashes.json and the
location map. All 19 mathematical Lean modules, verifier, pins and source bytes
remain unchanged. The canonical packet is assembled strictly from those 64
paths plus the named final-review/release evidence. The eight unmanifested
historical support files and untracked build/scratch files are excluded. In
particular no hand-written historical Checks.lean is consumed: the verifier
regenerates every check from candidate.json and the 19 source inventories.

The release paper changes two operational review-status sentences and corrects
the citation for T_ii=p_i to equations (2.2) with (5.6). No mathematical formula,
quantifier, proof, source convention or formal scope changed. Reviewed TeX/PDF
and QA originals are retained under reviewed-originals/.

The reviewer independently reproduced the parent 121-declaration/19-module
strict receipt byte for byte and read all actual types and axiom reports.
Fresh archive extraction and parent replay remain separate required steps.

Count scope: ONE complete source Conjecture5.2 resolution; coefficient families,
classical determinant/Jacobi/trace-log/multinomial tools, helper declarations and
finite checks receive no extra credit. No uniqueness of coefficients at fixed N
or algebraic independence is claimed. The coherent-amplitude convention is
source-forced; a separate literal nonnegative-principal-root endpoint is proved.

Novelty is bounded: no subsumer was found, but the semiseparable and full
Kostant--Toda search was selective, no exhaustive subscription-index search was
possible, and the reviewer had one functioning web engine. The MathDB unrelated
cross-references and unverifiable first-stated-year metadata are not relied on.
Actual published and arXiv source bodies were read. No worldwide priority claim.
''')
    (DEST / 'README.md').write_text('''# Complete peakon trace-power coefficient formula

This packet resolves Avan--Frappat--Ragoucy published Conjecture5.2, associated
with MathDB372008. One universal partition coefficient function works for every
particle number and positive trace power. The closed Lean endpoint is
PeakonCoefficients.source_conjecture_372008; the separate
nonnegative_source_conjecture_372008 covers literal principal square roots.

Read paper.pdf, PROOF.md, formal/SourceConclusion.lean and
reviews/final/review.md. Reproduce the strict replay with pinned Lean4.34.1 and
the pinned mathlib/packages directory:

    python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages

Expected:121 declarations,19 modules, all module logs empty, only propext,
Classical.choice and Quot.sound. Parent and independent receipts agree.
The archive requires its own fresh extracted replay before acceptance.

All64 reviewed originals are preserved with a location map. Only main.tex,
paper.pdf and paper-qa.json have release versions; all proof/verifier bytes are
unchanged. Historical candidate/checkpoint metadata retain credit0 and pending
statuses; this README and the final review supersede them. A post-extraction
acceptance.json is authoritative and is outside the immutable archive.

ONE source-question outcome only. Classical tools, helpers, the two already
conjectured coefficient families and finite checks are uncredited. Selective
semiseparable/Kostant--Toda and bounded citation/web coverage do not guarantee
worldwide priority. Unreliable MathDB companion metadata are not evidence.
''')
    print(DEST)


if __name__ == '__main__':
    main()
