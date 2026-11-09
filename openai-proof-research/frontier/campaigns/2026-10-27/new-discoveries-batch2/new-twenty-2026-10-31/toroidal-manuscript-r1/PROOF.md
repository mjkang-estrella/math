# MathDB 369421: complete finite refutation

DRAFT. AI-assisted preparation. Zero accepted credit; root alone accepts.

The exact target is the universal lower bound in Section 4, Conjecture 1,
Alshammari–Kitaev–Pyatkin, arXiv:2507.16469v1. The cached MathDB raw line is
preserved byte-identically, including its trailing newline; see
`mathdb-raw-receipt.json` for its SHA-256. The source defines linear-word
alternation, not circular alternation. The representation number minimizes
over positive uniformity and is infinity when no representation exists.

Use vertices `(r,c)` in `{0,1,2} × {0,1,2,3,4}`, labelled `5r+c`.
The complete literal word is in `verification.json`, `verify.py`, and the paper.
For each row and column add the forward cyclic edge in either coordinate;
canonicalize unordered pairs. This independently constructs all torus edges.

Every letter has exactly three occurrence positions. For any pair a < b,
filter the word to these letters. Alternation is equivalent to inequality
of every consecutive entry in that six-letter word, and also equivalent to
one of the two strict alternating orders on their three occurrence positions.
`verify.py` checks both equivalent criteria and compares them with the graph
for every pair. It asserts every equivalence, without importing any discovery
or review script. All edges pass and all nonedges fail. The full induced
subwords are retained; every nonedge includes a one-based location of two
equal consecutive entries. Thus the check is an exhaustive finite proof,
with every input exposed, rather than numerical extrapolation.

Consequently the word represents C_3 □ C_5 and the positive representation
minimum is at most three. The parameters satisfy both lower guards and
their sum equals eight. The conjecture would force a lower bound of four,
contradicting this upper bound. No equality claim is needed.

The formal definitions use Fin m × Fin n, the same cyclic adjacency,
filtered-list alternation, full-alphabet uniformity, and the least positive
uniformity in WithTop Nat. `number_le_three` supplies the minimum bridge;
`mathdb_369421 : ¬ Conjecture1` specializes the full guarded universal statement.
The current checker parses the coordinate literal from Witness.lean and
matches it to the displayed word. The packet is unchanged. The safe-extraction
receipt is fresh; Lean replays are inherited, explicitly identified evidence.

Review and root replay records report strict builds, explicit-module
leanchecker and metadata audits with only propext, Classical.choice and
Quot.sound. Cached upstream oleans and the installed toolchain are trusted;
no new Lean execution or full upstream rebuild is claimed here.

The significance is modest. Existing generic positional SMT search and a
representation-number tool are disclosed. The accepted journal manuscript
is embargoed and unread. Positive author/institutional linkage does not
certify exact accepted-body retention. Prior-art screens are bounded;
there is no priority claim, new-method claim, or separate neighbouring credit.
