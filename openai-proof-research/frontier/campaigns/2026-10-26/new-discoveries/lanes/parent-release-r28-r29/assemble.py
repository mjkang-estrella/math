#!/usr/bin/env python3
"""Assemble two manifest-only releases without changing reviewed originals."""
from pathlib import Path
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[2]

CONFIGS = [
    ('smale-unbounded', 'cstar-smale-unbounded', 27, 49, 5,
     'pi-smale-unbounded-final-review', 'candidate', 'parent49',
     ['final-math-check.py', 'final-math-check-output.txt']),
    ('cstar-bieberbach', 'cstar-bieberbach', 25, 28, 4,
     'pi-cstar-bieberbach-final-review', 'copy', 'parent28',
     ['math/final_checks.py', 'math/final-checks-run.log']),
]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    for lane_name, slug, count, decls, mods, reviewer, copy, receipt, extras in CONFIGS:
        lane = ROOT / 'lanes' / ('parent-' + lane_name)
        review = ROOT / 'lanes' / reviewer
        dest = ROOT / 'candidates' / slug
        assert not dest.exists(), dest
        hashes = json.loads((lane / 'final-review-hashes.json').read_text())
        assert len(hashes) == count
        for name, digest in hashes.items():
            assert sha(lane / name) == digest, name
            target = dest / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(lane / name, target)
        locations = dict((name, name) for name in hashes)
        for name in ['main.tex', 'paper.pdf', 'paper-qa.json']:
            original = dest / 'reviewed-originals' / name
            original.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(dest / name, original)
            locations[name] = str(original.relative_to(dest))
        (dest / 'reviewed-parent-hashes.json').write_text(json.dumps(hashes, indent=2)+'\n')
        (dest / 'reviewed-file-locations.json').write_text(json.dumps(locations, indent=2)+'\n')
        for name in ['review.md', 'provenance.json'] + extras:
            target = dest / 'reviews/final' / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(review / name, target)
        parent_audit = lane / 'verification' / (receipt + '-audit.json')
        independent_audit = review / copy / 'build/verified/audit.json'
        assert parent_audit.read_bytes() == independent_audit.read_bytes()
        audit = json.loads(parent_audit.read_text())
        assert audit['status'] == 'PASS' and audit['declarations'] == decls
        assert len(audit['modules']) == mods
        shutil.copyfile(parent_audit, dest / 'verification/parent-audit.json')
        shutil.copyfile(independent_audit, dest / 'verification/independent-audit.json')
        shutil.copyfile(review / copy / 'build/verified/Checks.log',
                        dest / 'verification/independent-Checks.log')
        source = (dest / 'main.tex').read_text()
        if slug == 'cstar-smale-unbounded':
            old = '''Independent preliminary mathematical and substantive-eligibility review
passes, with a bounded novelty screen; complete final review is pending.
Eligibility is solely as a new infinite-class theorem, not credit for an
unresolved source question. Discovery credit is zero. The rejected fixed constant-one witness is not
counted, and the parameter family is at most one prospective outcome.'''
            new = '''Independent final source, mathematical, formal, manuscript and bounded
novelty review passes. Eligibility is solely as a new infinite-class theorem,
not credit for an unresolved source question. Acceptance also requires a fresh
replay of the extracted proof archive. The rejected fixed constant-one witness
is not counted; the parameter family is one combined outcome.'''
            notes = '''The parent independently weighs and accepts the substantive-eligibility
case, conditional on a fresh extracted replay: fixed degree three, a single
connected function algebra, every finite proposed constant defeated, actual
existing two-element critical set, invertible test derivative. The fact that
parameterization is modest labor does not remove the new quantifier or the
scalar-finite / fixed-algebra-infinite distinction. This is ONE family theorem,
absorbing the rejected fixed witness which remains credit0; no first resolution
of the already-publicly-refuted constant-one source question is claimed. No
HIGHERMEAN or DUALSMALE side effect receives credit. Generic selection lemmas
are reused, credited infrastructure, not new outcomes.

Two ancillary review phrases are not adopted: an infinity theorem implies a
fixed-constant existential counterexample (though it need not identify the old
specific witness), and the source/registry does discuss connected-case open
directions, so the review's phrase that no registry asks such a question is too
broad. Neither issue affects the literal Lean theorem. Preliminary corrections
about the old CxC family and the non-exact scalar Smale constant remain binding.
'''
            title = 'No finite C*-Smale mean-value constant at fixed degree three'
        else:
            old = '''Independent preliminary source, mathematical, bounded prior-art and
substantive-eligibility review passes; complete final review is pending.'''
            new = '''Independent final review passes all five gates, with bounded novelty coverage.
'''
            assert old in source
            source = source.replace(old, new)
            old = '''Discovery credit remains zero. The two variants use one
construction and constitute at most one prospective outcome.'''
            new = '''Acceptance additionally requires a fresh replay of the extracted proof
archive. The two variants use one construction and constitute one outcome.'''
            notes = '''ONE source-question outcome combines the general-coefficient
Conjectures1.2/1.4. The fixed parameter8t is formalized; no parameter-family
or invertible-coefficient/polynomial/Robertson/Lebedev-Milin side credit.

Parent clarification of two ancillary reviewer phrases: CStarRing is a norm/star
class and does not itself impose an order. The claim uses the actual pointwise
ComplexOrder on C([0,1],C), with its genuine StarOrderedRing compatibility;
this is the source positive-cone order. The explicit elementwise calculation
at t=1 proves the violation. Also the witness has scalar-fiber zeros, not a
second global zero element (it is globally injective with F(0)=0). For example
u(t)=pi*i/4 has norm<1 and F(u)(1)=0 while u(1)!=0, so an invertible exponential
multiplier factorization cannot hold. Neither ancillary wording is relied on
by the Lean endpoint or the manuscript.

Actual author-deposited Zenodo6917925 bytes are used; directPreprints403 remains
a disclosed limit. Whole-text agreement and fresh live deposit checksum were
verified, but binary identity of the deposits is not claimed.
'''
            title = 'Globally injective C*-power series violating Bieberbach order bounds'
        assert old in source
        (dest / 'main.tex').write_text(source.replace(old,new))
        (dest / 'reviews/parent-final-addendum.md').write_text(
            '# Parent reconciliation of independent final review\n\n'
            f'All five gates pass on the {count}-path freeze at '
            '14493cae8ab4b17d74fbff135054816d576bfcc7. The parent read the actual '
            'review and replay evidence. All reviewed originals are preserved with '
            'a location map. All Lean/verifier/pin/source bytes are unchanged. Only '
            'operational review-status sentences in the release paper change. '
            'Historical credit0/pending metadata remain historical.\n\n'+notes+
            '\nBounded novelty evidence cannot guarantee worldwide priority; '
            'all actual review access/search limits stay attached. No external '
            'posting or communication. Fresh extracted replay remains required.\n')
        (dest / 'README.md').write_text(
            '# '+title+'\n\nRead paper.pdf, PROOF.md, the formal source endpoint, '
            'reviews/final/review.md and reviews/parent-final-addendum.md.\n\n'
            'Reproduce with pinned Lean4.34.1 and the packages in verification/pins.json:\n\n'
            '    python3 verification/verify_candidate.py . --lean-bin /path/to/lean '
            '--packages /path/to/.lake/packages\n\n'
            f'Expected: {decls} declarations in {mods} modules, all module logs empty, '
            'only propext/Classical.choice/Quot.sound. Parent and fresh independent '
            'receipts agree. The immutable archive still requires a fresh extracted replay.\n\n'
            f'All {count} reviewed originals are preserved. Only the release TeX/PDF/QA '
            'are updated for final-review status; proof/verifier bytes are unchanged. '
            'The later acceptance.json outside the archive governs any discovery count. '
            'Historical credit0/pending snapshots do not assert present acceptance.\n\n'+notes)
        print(dest)

if __name__ == '__main__':
    main()
