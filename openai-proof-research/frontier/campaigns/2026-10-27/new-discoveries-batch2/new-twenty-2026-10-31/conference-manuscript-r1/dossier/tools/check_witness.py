"""Independent exact check of the MathDB 324342 witness (Python stdlib only; no Lean).

    python3 -I -B check_witness.py 324342-replay-fit-source.zip OUT.json

Reads the Lean endpoint module directly from the source ZIP (in memory, nothing is
extracted), parses Wrows / coeff / word / Blist / Dlist, and verifies, with exact integer
arithmetic mod 19:
  * W is a 20x20 {0,+1,-1} matrix, zero diagonal, skew (W^T = -W), 19 nonzeros in every
    row and column, W W^T = 19 I  (a skew conference matrix; the source's weighing-matrix
    definition with w = n - 1 and the textbook definition);
  * W equals H - I for the Goethals-Seidel array H built from four +-1 sequences of length 5,
    whose periodic autocorrelations sum to 0 at every nonzero shift;
  * rank over F_19 is 10 by fresh Gaussian elimination (no supplied certificate used);
    W W^T = 0 mod 19 (self-orthogonality gives rank <= 10 by hand);
  * the leading 10x10 block A has inverse B (both orders); every row equals D times rows 0..9;
  * word = sum_i coeff_i * row_i (mod 19) has Hamming weight 9, so d <= 9 < 11 = 20 - 10 + 1;
  * the Arasu-Gulliver congruences alpha^2 + 19 = 0 and alpha^2 + beta^2 + 19 = 0 (mod 19)
    have no solutions with alpha, beta nonzero.
"""
import hashlib, json, re, sys, zipfile

P, N = 19, 20
arc, out = sys.argv[1], sys.argv[2]
src = zipfile.ZipFile(arc).read('ConferenceMDS324342.lean').decode()


def lean_list(name, nested):
    """Innermost bracketed integer lists inside the declaration `def name ...` (up to the blank line)."""
    start = src.index('\ndef ' + name + ' ')
    block = src[start:src.index('\n\n', start + 1)]
    lists = [[int(x) for x in body.split(',')] for body in re.findall(r'\[([-\d,\s]+)\]', block)]
    return lists if nested else lists[0]


W = lean_list('Wrows', True)
coeff = lean_list('coeff', False)
word = lean_list('word', False)
B = lean_list('Blist', True)
D = lean_list('Dlist', True)
assert len(W) == N and all(len(r) == N for r in W)
assert len(coeff) == N and len(word) == N and len(B) == 10 and len(D) == N

T = [list(c) for c in zip(*W)]
mul = lambda X, Y: [[sum(X[i][t] * Y[t][j] for t in range(len(Y))) for j in range(len(Y[0]))] for i in range(len(X))]
G = mul(W, T)
res = {
    'archive_sha256': hashlib.sha256(open(arc, 'rb').read()).hexdigest(),
    'lean_module_sha256': hashlib.sha256(src.encode()).hexdigest(),
    'entries_in_0_pm1': all(x in (0, 1, -1) for r in W for x in r),
    'zero_diagonal': all(W[i][i] == 0 for i in range(N)),
    'offdiag_pm1': all(W[i][j] in (1, -1) for i in range(N) for j in range(N) if i != j),
    'skew': all(W[j][i] == -W[i][j] for i in range(N) for j in range(N)),
    'row_nonzeros': sorted({sum(1 for x in r if x) for r in W}),
    'col_nonzeros': sorted({sum(1 for x in c if x) for c in T}),
    'gram_is_19I': all(G[i][j] == (19 if i == j else 0) for i in range(N) for j in range(N)),
}

# Goethals-Seidel reconstruction
m = 5
seqs = {'a': [1, 1, 1, -1, -1], 'b': [1, 1, 1, 1, -1], 'c': [1, 1, 1, 1, -1], 'd': [1, 1, -1, 1, -1]}
paf = lambda s, t: sum(s[i] * s[(i + t) % m] for i in range(m))
circ = lambda r: [[r[(j - i) % m] for j in range(m)] for i in range(m)]
tr = lambda X: [list(r) for r in zip(*X)]
neg = lambda X: [[-x for x in r] for r in X]
R = [[int(i + j == m - 1) for j in range(m)] for i in range(m)]
A_, B_, C_, D_ = (circ(seqs[k]) for k in 'abcd')
BR, CR, DR = mul(B_, R), mul(C_, R), mul(D_, R)
blocks = [[A_, BR, CR, DR],
          [neg(BR), A_, mul(tr(D_), R), neg(mul(tr(C_), R))],
          [neg(CR), neg(mul(tr(D_), R)), A_, mul(tr(B_), R)],
          [neg(DR), mul(tr(C_), R), neg(mul(tr(B_), R)), A_]]
H = [sum((blocks[I][J][i] for J in range(4)), []) for I in range(4) for i in range(m)]
res['gs_sequences'] = seqs
res['gs_paf_by_sequence'] = {k: [paf(s, t) for t in range(1, m)] for k, s in seqs.items()}
res['gs_paf_sums_t1_to_t4'] = [sum(paf(s, t) for s in seqs.values()) for t in range(1, m)]
res['gs_a_skew_type'] = seqs['a'][0] == 1 and all(seqs['a'][m - i] == -seqs['a'][i] for i in range(1, m))
res['W_equals_H_minus_I'] = all(W[i][j] == H[i][j] - (i == j) for i in range(N) for j in range(N))


def rank_mod(M, p):
    M = [[x % p for x in r] for r in M]
    rk, cols = 0, len(M[0])
    for c in range(cols):
        piv = next((r for r in range(rk, len(M)) if M[r][c]), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], p - 2, p)
        M[rk] = [x * inv % p for x in M[rk]]
        for r in range(len(M)):
            if r != rk and M[r][c]:
                f = M[r][c]
                M[r] = [(x - f * y) % p for x, y in zip(M[r], M[rk])]
        rk += 1
    return rk


res['rank_mod_19_gauss'] = rank_mod(W, P)
res['self_orthogonal_mod_19'] = all(G[i][j] % P == 0 for i in range(N) for j in range(N))
Am = [r[:10] for r in W[:10]]
I10 = [[int(i == j) for j in range(10)] for i in range(10)]
res['A_times_B_is_I_mod_19'] = [[x % P for x in r] for r in mul(Am, B)] == I10
res['B_times_A_is_I_mod_19'] = [[x % P for x in r] for r in mul(B, Am)] == I10
DW = mul(D, W[:10])
res['rows_equal_D_times_rows_0_to_9_mod_19'] = all((DW[r][j] - W[r][j]) % P == 0 for r in range(N) for j in range(N))
integer_comb = [sum(coeff[i] * W[i][j] for i in range(N)) for j in range(N)]
reduced = [x % P for x in integer_comb]
res['coefficients'] = coeff
res['integer_combination'] = integer_comb
res['word_from_combination'] = reduced
res['word_matches_lean_word'] = reduced == [x % P for x in word]
res['word_support'] = [j for j in range(N) if reduced[j]]
res['word_weight'] = len(res['word_support'])
res['rows_used'] = [i for i in range(N) if coeff[i] % P]
k = res['rank_mod_19_gauss']
res['singleton_value_n_minus_k_plus_1'] = N - k + 1
res['conjectured_distance_(p+3)/2'] = (P + 3) // 2
res['conjectured_dimension_(p+1)/2'] = (P + 1) // 2
squares = sorted({x * x % P for x in range(1, P)})
res['nonzero_squares_mod_19'] = squares
res['minus_one_is_square_mod_19'] = (P - 1) in squares
res['ag_alpha_solutions'] = [a for a in range(1, P) if (a * a + 19) % P == 0]
res['ag_alpha_beta_solutions'] = [(a, b) for a in range(1, P) for b in range(1, P) if (a * a + b * b + 19) % P == 0]
# column normalisation (source's normal form): multiply column j by the sign of W[0][j] (+1 at the zero)
sg = [W[0][j] if W[0][j] else 1 for j in range(N)]
res['normal_form_first_row'] = [W[0][j] * sg[j] for j in range(N)]
res['normal_form_word_weight'] = sum(1 for j in range(N) if (reduced[j] * sg[j]) % P)
checks = ['entries_in_0_pm1', 'zero_diagonal', 'offdiag_pm1', 'skew', 'gram_is_19I', 'gs_a_skew_type',
          'W_equals_H_minus_I', 'self_orthogonal_mod_19', 'A_times_B_is_I_mod_19', 'B_times_A_is_I_mod_19',
          'rows_equal_D_times_rows_0_to_9_mod_19', 'word_matches_lean_word']
ok = (all(res[c] for c in checks) and res['row_nonzeros'] == [19] and res['col_nonzeros'] == [19]
      and res['gs_paf_sums_t1_to_t4'] == [0, 0, 0, 0] and k == 10 and res['word_weight'] == 9
      and res['singleton_value_n_minus_k_plus_1'] == 11 == res['conjectured_distance_(p+3)/2']
      and not res['minus_one_is_square_mod_19'] and not res['ag_alpha_solutions'] and not res['ag_alpha_beta_solutions'])
res['ALL_CHECKS_PASS'] = ok
res['matrix_W'] = W
res['inverse_B'] = B
res['scope'] = 'ordinary exact arithmetic; complements but does not replace the kernel-checked Lean proof'
json.dump(res, open(out, 'w'), indent=1)
print('ALL_CHECKS_PASS', ok, 'rank', k, 'weight', res['word_weight'], 'support', res['word_support'])
sys.exit(0 if ok else 1)
