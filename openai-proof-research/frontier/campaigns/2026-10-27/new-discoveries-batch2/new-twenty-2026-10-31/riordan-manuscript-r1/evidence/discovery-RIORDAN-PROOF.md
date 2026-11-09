# Candidate refutation of MathDB 338258

Not accepted; independent root review required.

Source: Cheon–Jung–Kitaev–Mojallal, *Riordan graphs II: Spectral properties*, arXiv:1801.07021v1 (the only arXiv version), Definition 2.2, Definition 2.9, Conjecture 7.7. The journal manuscript downloaded from the Strathclyde institutional repository retains Conjecture 7.7. Both full PDFs and HTTP/hash receipts are in sources/.

Take n = 15 and

    g(z) = 1 + z + z^3 + z^6 + z^7 + z^8 + z^12 + z^13.

Define the simple graph G_15(g,zg) by the source's binary Riordan adjacency formula. With zero-based vertices i,j, its diagonal is zero and its off-diagonal entry is

    a(i,j) = ([z^(max(i,j))] (zg)^(min(i,j)+1)) mod 2
           = ([z^(max(i,j)-min(i,j)-1)] g^(min(i,j)+1)) mod 2.

This is exactly B(zg,zg) + B(zg,zg)^T, because B(zg,zg) is strictly lower triangular. The explicit matrix is preserved in outputs/riordan-witness.json. Its constant coefficient is 1, so this is a proper Bell-type graph. Direct coefficient computations verify that a(2i+1,2j+1) = 0 for 0 <= i,j < 7, and a(2i,2j) = a(i,j) for 0 <= i,j < 8. Thus the even-induced graph is null and the odd-induced graph is exactly G_8(g,zg), with the canonical relabeling. These are the two conditions in Definition 2.9; no infinite-series extension or classification lemma is assumed.

Now take the following vector, in source vertex order 1,...,15:

    x = (-1, 1, 0, 0, -1, 1, 0, 1, 1, -2, 0, 1, 1, -1, 1).

Multiplication by the displayed 0/1 matrix gives A x = 0 in every coordinate. Since x_1 = -1, this is a nonzero real zero-eigenvector, and its odd-index subvector is nonzero. In fact that subvector is (-1,0,-1,0,1,0,1,1). This refutes Conjecture 7.7 in the exact intended finite-graph setting. The proof does not depend on the claimed equivalence in Theorem 7.8 or on correcting another source theorem.

Search provenance: exhaustive binary g-prefix generation (g_0 = 1 and g_(2j+1) = g_j) through n = 14, then n = 15 masks 0 through 44 inclusive. Modular ranks were used as diagnostics; the witness ranks and kernel vector were recomputed over rational numbers and the actual kernel product over integers. No global minimality claim is made from a modular non-finding. The generated family is a subset of valid finite io-decomposable graphs and may not exhaust all finite exceptional prefixes. The polynomial witness itself is checked directly, rather than relying on this generator.

Novelty limits: dated web queries by paper title, conjecture number, odd kernel and nullity found the source and no matching explicit example. The current Omega D5/Problems path listings and unchanged OpenAI/math HEAD were checked. A path screen is not a reading of every proof; worldwide novelty is not established. The witness is not the Pascal or Catalan graph (its coefficient prefix differs from both), and no classical extremal graph mechanism is used. Root must adjudicate significance, source fidelity and bounded prior art independently.
