# H004 early practical screen: paired outputs and terminal y omission are prior art

Verified improvement remains NONE. Native Sol's independent practical ideation
identified and then rejected two apparent savings after checking primary prior
art. Root independently read the paper and source. This is a baseline correction,
not a new ECDLP algorithm, benchmark or code contribution.

[Galbraith–Wang–Zhang, Computing elliptic curve discrete logarithms with improved
baby-step giant-step algorithm](https://pdfs.semanticscholar.org/5753/7e7d4d08b6de01aa79717c4bb849e694958f.pdf),
AMC11(2017), DOI10.3934/amc.2017038, §4.1 describes shared-inversion paired
addition. Algorithm2/§4.3 generates blocks; §5 uses x-coordinates in BSGS and
charges delayed collision detection caused by batching. Their quoted field-cost
constants assume a particular inversion/multiplication/squaring model. They are
not measured costs in this project or evidence of full-size memory feasibility.

Merely computing both P+T and P−T, or generating x-coordinate blocks, therefore
cannot be counted as a new saving. The paper's full-coordinate arithmetic may
suggest omitting y at terminal satellite points, retaining it only for the next
block center and recovering the sign after a collision. That too is implemented
in existing primary source: [keyhunt.cpp](https://raw.githubusercontent.com/albertobsd/keyhunt/main/keyhunt.cpp),
`thread_process_bsgs`, viewed2026-10-08. Its grouped inversion feeds both satellite
branches, both satellite y computations are disabled with `#if 0`, and the next
center's y is computed. Root inspected that code, including collision checking.
This file is a moving branch reference; no immutable revision is claimed here.

No third-party executable was built or run, and no wallet/target data was used.
Source inspection establishes prior implementation, not correctness, throughput,
or a suitable full-domain benchmark for our challenge. The stronger comparator
must allow these arithmetic omissions along with known batching/negation tricks.
No experiment is justified merely to rediscover the savings against an artificially
unoptimized comparator. Remaining practical mechanisms still need useful-collision
density, memory, preprocessing, exceptional-point and recovery-cost accounting.

Retrieval notes: root web fetch of eprint2015/605.pdf returned403; the cited final
paper mirror succeeded. GitHub's raw redirect failed, then the direct
raw.githubusercontent.com source succeeded. No fabricated claim of a successful
fetch or runtime. The native proposer continues its remaining distinct cards;
this early screen does not prejudge them.
