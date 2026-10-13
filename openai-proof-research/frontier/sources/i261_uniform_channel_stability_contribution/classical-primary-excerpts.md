# Classical primary statement excerpts and reading notes

These are short mathematical transcriptions and original paraphrases of fully read primary passages, not copies of unread papers. Full-response identities and precise extents appear in input-authentication.json.

## Hundertmark–Laptev–Weidl

Primary: https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf . PDF pages 3–6 were rendered and read in full, including all formulas and the complete presented proof of Theorem 3.1.

For a nonpositive operator-valued V, with V(x) trace class almost everywhere and integrable trace of V_-, the theorem states

    sum_j sqrt(E_j) <= (1/2) integral tr V_-.

The ambient space is L2(R;G). Page 3 specifies the form realization; page 4 states the theorem and Ky Fan majorization lemma. Pages 5–6 establish monotonicity by unitary averaging with Cauchy distributions, then use Birman–Schwinger and partial-trace monotonicity to prove the bound. Substituting V=-B_w w ff^T meets these hypotheses for every finite channel number, since its trace is integrable. No smoothness or compact support hypothesis is in Theorem 3.1. Sections after the opening sentence of 3.4 were not read or used. The theorem and its argument are classical inputs.

## Carlen–Frank–Lieb

Primary: https://arxiv.org/html/1301.5032v2 . Theorem 2.2(i), for d=1 and s=gamma+1/2<=2, has the form

    |lambda(V)|/(integral V_-^s)^(1/gamma)
      <= C_(gamma,1) [1-c inf_(W in M) ||V_--W_-||_s^2/||V_-||_s^2].

Here V is scalar and lambda is its lowest eigenvalue. Theorem 5.1 supplies scalar GNS stability in squared H1 distance. Its full Section 5 proof centers at the optimizer, identifies the Hessian kernel and absorbs higher-order remainders. It contains no statement controlling a matrix orientation field or additional eigenvalue moments.

## Leng

Primary: https://arxiv.org/html/2606.03749 . Theorem 1.2 replaces the scalar CFL distance with

    inf_(W in M) (integral |P_V-P_W|)^2,
    P_V=V_-^s/(integral V_-^s).

The spectral statements and their proof, through the end of Theorem 1.2, were read. They concern scalar lowest-eigenvalue stability; later convex-geometric proofs were not read or used.

## Frank–Gontier–Lewin

Primary: https://arxiv.org/pdf/2109.05984 . PDF pages 5–10 were extracted and read in full. Section 2 states scalar finite-rank optimizer existence, bubble decomposition and Euler–Lagrange results. Theorem 5 at gamma=3/2,d=1 gives convergence of maximizing sequences to the KdV soliton manifold, without a quantitative deficit rate. Its channel count is a scalar eigenvalue truncation, not a matrix internal dimension. These statements do not subsume I262. Proofs elsewhere in this paper were not read or relied on.
