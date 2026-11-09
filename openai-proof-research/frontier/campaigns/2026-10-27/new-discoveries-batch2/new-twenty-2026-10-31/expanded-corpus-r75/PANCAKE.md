# MathDB 382220: genus-two rotation lead, not a full Lean solution

The literal source Conjecture 4.4 predicts gamma(P4)=3. P4 has the 24 permutations of 1234 as vertices and edges reversing prefixes of lengths 2,3,4, so it is a connected cubic simple graph with 36 edges. At each vertex there are exactly two cyclic rotations of the three incident generators. Global reversal preserves face counts, so fix one vertex's rotation and enumerate all 2^23 remaining choices.

scripts/pancake.c performs this exhaustive search; logs/pancake.log contains its full output and resource receipt. Histogram of faces (modulo global reversal):

    F=2: 4953376
    F=4: 3194672
    F=6: 238178
    F=8: 2376
    F=10: 6

Mask 2987801 (permutations in lexicographic order, generators 2,3,4, bit 1 reverses the local cyclic order) yields 10 faces. Independent Python code scripts/certificates.py reconstructs the 72-dart face permutation and lists all ten orbits in outputs/pancake-certificate.json. Standard orientable ribbon-surface gluing caps each boundary cycle with a disk, giving Euler characteristic 24-36+10=-2 and genus 2. Thus this is an ordinary mathematical refutation of the displayed genus-three claim, subject to source/version checks. The exhaustive histogram also suggests exact genus two, but only the upper bound is needed for refutation.

The author paper's Remark 4.3 / Conjecture 4.4 and its rotation-system definitions were read in the actual served arXiv PDF. OpenAlex identifies a later journal version DOI 10.1016/j.dam.2025.11.003. The DOI returned a redirect page; the publisher body returned 403. It was not retried or bypassed. The later same-author spectra paper 2506.08345 was fetched and its principal matrix/spectral statements inspected: it does not itself supply a surface embedding theorem. No worldwide priority clearance is claimed.

Remaining critical gaps: actual journal/correction body comparison; broader author/citing literature; a FULL Lean bridge from the certified combinatorial rotation system to an orientable topological surface embedding and the source graph's genus. No face-count predicate is presented as a literal Lean genus theorem. There is no Lean endpoint or credit for this route.
