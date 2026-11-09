# Exact proof dossier: MathDB 341850

DRAFT with AI assistance. No human authors, affiliations, new general obstruction
or priority claim. Journal version of record unread; retention not certified.

## Setting and theorem

Index outputs by all subsets S of [d] with |S|<=r, including empty S.
phi(x) records their monomials, and F is its image. Submodularity is
f(A intersect B)+f(A union B)<=f(A)+f(B).
At (r,d)=(2,5), n=1+5+10=16, no submodular integer function has f<=-1 on F
and f>=0 off F. Thus preprint Conjecture 3.33 fails without its evaluation clause.

## Shortest proof, applying Elbracht-Kneip-Teegen

On the constant-one face, bit labels (least significant first) are
0,1,2,3,4,01,02,03,04,12,13,14,23,24,34.
Good masks contain exactly all pairs of their singleton support.
The review supplies these four outer dependency edges:

| a | b | good c | meet | join | bad companion |
|---:|---:|---:|---:|---:|---:|
| 103 | 5743 | 5646 | 6 | 5743 | 6 |
| 5743 | 1067 | 19899 | 1067 | 24575 | 24575 |
| 1067 | 5359 | 4301 | 9 | 5359 | 9 |
| 5359 | 103 | 11127 | 103 | 16383 | 16383 |

All a,b and companion masks are bad. For every row submodularity implies
h(b)<=h(a)+h(c)-h(companion)<=h(a)-1. The endpoints form a cycle, so summing
gives 0<=-4. This applies Elbracht, Kneip and Teegen, The Structure of Submodular
Separation Systems, arXiv:2103.13162v2, Lemma 4.1 and Corollary 4.2.
It even excludes real-valued separators with these quantitative signs.
Shortest describes the proof presented, not certified graph-girth minimality.

## Independent symmetric proof (the supplied Lean argument)

Define g(m)=sum_sigma h(sigma m) over all 120 permutations. Coordinate renaming
preserves meet, join and goodness; g is submodular and orbit invariant, <=-120
on good masks and >=0 on bad masks. The complete weighted support follows.
For submodular rows, terms are (meet,+1),(join,+1),(a,-1),(b,-1).
Good rows contribute +weight*g(point); bad rows contribute -weight*g(point).

    [
      {
        "kind": "submodular",
        "terms": [
          [
            7167,
            1
          ],
          [
            16383,
            1
          ],
          [
            8191,
            -1
          ],
          [
            15359,
            -1
          ]
        ],
        "weight": 1
      },
      {
        "kind": "submodular",
        "terms": [
          [
            2203,
            1
          ],
          [
            16383,
            1
          ],
          [
            15327,
            -1
          ],
          [
            3259,
            -1
          ]
        ],
        "weight": 1
      },
      {
        "kind": "submodular",
        "terms": [
          [
            29,
            1
          ],
          [
            30719,
            1
          ],
          [
            28957,
            -1
          ],
          [
            1791,
            -1
          ]
        ],
        "weight": 1
      },
      {
        "kind": "submodular",
        "terms": [
          [
            6,
            1
          ],
          [
            527,
            1
          ],
          [
            518,
            -1
          ],
          [
            15,
            -1
          ]
        ],
        "weight": 1
      },
      {
        "kind": "submodular",
        "terms": [
          [
            6,
            1
          ],
          [
            559,
            1
          ],
          [
            518,
            -1
          ],
          [
            47,
            -1
          ]
        ],
        "weight": 1
      },
      {
        "kind": "submodular",
        "terms": [
          [
            6,
            1
          ],
          [
            5679,
            1
          ],
          [
            5646,
            -1
          ],
          [
            39,
            -1
          ]
        ],
        "weight": 1
      },
      {
        "kind": "submodular",
        "terms": [
          [
            6,
            1
          ],
          [
            5759,
            1
          ],
          [
            5646,
            -1
          ],
          [
            119,
            -1
          ]
        ],
        "weight": 1
      },
      {
        "kind": "submodular",
        "terms": [
          [
            526,
            1
          ],
          [
            5775,
            1
          ],
          [
            5646,
            -1
          ],
          [
            655,
            -1
          ]
        ],
        "weight": 1
      },
      {
        "kind": "submodular",
        "terms": [
          [
            518,
            1
          ],
          [
            32383,
            1
          ],
          [
            32286,
            -1
          ],
          [
            615,
            -1
          ]
        ],
        "weight": 2
      },
      {
        "kind": "bad",
        "point": 3,
        "weight": 4
      },
      {
        "kind": "good",
        "point": 615,
        "weight": 5
      },
      {
        "kind": "good",
        "point": 5871,
        "weight": 2
      },
      {
        "kind": "bad",
        "point": 16383,
        "weight": 3
      }
    ]

All expanded coefficients on actual masks cancel. Good weight 5+2=7 yields
-600-240=-840, so 0<=-840. The fresh script derives actions from definitions,
ignoring supplied orbit tables. Full receipt: receipts/recomputation.json.

## Small feasible cases and formal correspondence

Four supplied face vectors are rationally reconstructed and checked with exact
Fraction arithmetic. Elementary two-bit inequalities imply full submodularity
by telescoping diminishing returns. H(z,m)=h(m)+C*(1-z), C>=-min h, is submodular,
nonnegative on the constant-zero slice, and agrees on the constant-one face.
Clearing denominators gives integer full-cube witnesses in receipts/witness-d-r.json.

Separator.lean models the entire allowed Boolean lattice by subset-labeled
coordinates; phi is filtered powerset and includes empty. Certificate.lean
embeds the face, proves actual permutation identities and the symmetric
contradiction, then proves:
Separation.source_existence_refuted : not Separation.SeparationExistence.
The universal assertion ranges over every d,r with r<=d. Specialization at
d=5,r=2 refutes bare existence, hence the stronger evaluation-time assertion.
A separate numeric-coordinate bijection and complexity model are not formalized.

The six-member packet is byte-identical. Strict replays, 45-declaration audits
and allowed axioms (propext, Classical.choice, Quot.sound) are recorded evidence;
this task executed no formal checker. See receipts/parent-final.json for root
replay and bounded registry screen, including the extraction-path oddity.
Upstream mathlib is trusted, not fully rebuilt.

The result blocks the universal separator premise of the proposed
SUBMOD-MIN-MOD_M reduction (Proposition 3.34, Corollary 3.35), not the
optimization problem itself. Source quotation and references: paper.ms/PDF.
The unread journal and non-exhaustive prior-art review remain limitations.
