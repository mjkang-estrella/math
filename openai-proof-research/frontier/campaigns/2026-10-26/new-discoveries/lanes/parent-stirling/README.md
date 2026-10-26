# Type-B q-Stirling parity log-concavity: exploratory screen

Credit: **0**. No proof or counterexample found.

Source: Sagan–Swanson, *q-Stirling numbers in type B*, arXiv2205.14078 and published European Journal of Combinatorics118(2024),103899. Published primary PDF was read through the web tool, including Definition1.5 and Conjecture7.5. The local publisher request returned a 212-byte non-PDF challenge; it is explicitly named `qStB-pub.failed-response.txt`. The actual arXiv PDF was retrieved separately, SHA256 13a3f811c6b67e41bf9c74fb3be55235ada68fc9ffef5b44ddd5c8346020e159.

The literal recurrences are S[n,k]=S[n−1,k−1]+[2k+1]S[n−1,k] and c[n,k]=c[n−1,k−1]+[2n−1]c[n−1,k], with initial delta row. Parity log-concavity means coefficient[j]^2≥coefficient[j−2]coefficient[j+2]. The source reports checks through n50.

`python3 search.py --limit 120` constructs every polynomial by exact Python integer arithmetic, with sliding sums for multiplication by a q-integer. It checks every interior parity log-concavity inequality for both triangles through n120: **52,657,146 checks, no counterexample**, about21 seconds on this host. Boundary cases outside the polynomial support are automatically nonnegative. This finite search does not establish the universal conjecture, nor numerical novelty, and receives no credit. `search-result.json` and `search.log` record the result.

The live MathDB354787 snapshot has status open, no progress and empty solutions. A separate 2026 paper resolving bottom-heaviness appeared in searches; that is a different source conjecture and was not counted or adopted as a new result here.
