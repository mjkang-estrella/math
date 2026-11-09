"""Independent implementation of Berlow's s_T map (arXiv:2008.01164v2, Def 1.3).

Semantics (derived independently from the source text):
  - Input read left to right. At each step look at the next input element x.
  - If pushing x keeps the stack T-avoiding when the stack is read TOP-TO-BOTTOM
    (x becomes the new top), push x and advance the input pointer.
  - Otherwise pop the current top of the stack to the output; the input element x
    is retried (pointer does not advance).
  - When the input is exhausted, pop the whole stack (top first) to the output.

Calibration facts from the source used to validate (all proved there):
  (V1) Theorem 2.3: if pi avoids T^r then s_T(pi) = pi^r.
  (V2) Theorem 1.5: if T is reduced and closed under sigma -> hat(sigma) then
       s_T is a bijection with inverse r . s_T . r.
  (V3) Lemma 4.3 + Theorem 4.5: periodic points of s_{123,132} are exactly the
       half-decreasing permutations (Def 4.2).
  (V4) Corollary 4.9: periodic points of s_{312,321} are exactly the
       half-increasing permutations (complements of half-decreasing).

Patterns of length 3 only are needed for the target; push-check is O(depth).
"""
import itertools


def word_contains(word, pat):
    """True if the word (list of ints) has a subsequence order-isomorphic to pat."""
    m, k = len(word), len(pat)
    if m < k:
        return False
    for idx in itertools.combinations(range(m), k):
        sub = [word[i] for i in idx]
        if _ranks(sub) == _ranks(pat):
            return True
    return False


def _ranks(els):
    order = sorted(range(len(els)), key=lambda i: els[i])
    r = [0] * len(els)
    for pos, i in enumerate(order):
        r[i] = pos
    return tuple(r)


def _push_blocked(x, rev_stack, pats):
    """rev_stack is the stack read top-to-bottom. Pushing x makes word [x]+rev_stack.
    Only triples involving x can newly create a pattern. Return True if blocked."""
    # check (x, w_i, w_j) for all i<j  (w_i above w_j)
    n = len(rev_stack)
    p1 = pats[0]  # e.g. (1,3,2)
    p2 = pats[1]
    for j in range(n):
        wj = rev_stack[j]
        for i in range(j):
            wi = rev_stack[i]
            # triple (x, wi, wj): blocked iff ~=(1,3,2) or ~=(2,1,3)
            sig = _sig3(x, wi, wj)
            if sig == p1 or sig == p2:
                return True
    return False


def _sig3(a, b, c):
    if a < b:
        if b < c:
            return (0, 1, 2)   # 123
        elif a < c:
            return (0, 2, 1)   # 132
        else:
            return (1, 2, 0)   # 231
    else:  # a > b
        if a < c:
            return (1, 0, 2)   # 213
        elif b < c:
            return (2, 0, 1)   # 312
        else:
            return (2, 1, 0)   # 321


def s_T(perm, pats):
    """Simulate s_T. perm: tuple. pats: tuple of length-3 patterns (tuples, 1-based)."""
    pats = tuple(_ranks(list(p)) for p in pats)  # normalize to 0-based rank sigs
    stack = []          # index 0 = top? NO: we keep rev_stack for the word read top-to-bottom
    rev_stack = []      # stack read top-to-bottom: rev_stack[0] = top
    out = []
    i = 0
    n = len(perm)
    while i < n:
        x = perm[i]
        if not _push_blocked(x, rev_stack, pats):
            rev_stack.insert(0, x)  # x becomes new top
            i += 1
        else:
            out.append(rev_stack.pop(0))  # pop current top
    out.extend(rev_stack)
    return tuple(out)


def reverse_word(p):
    return tuple(reversed(p))


def complement(p):
    n = len(p)
    return tuple(n + 1 - v for v in p)


def hat(p):
    """hat(sigma) = sigma(2) sigma(1) sigma(3) ... sigma(k)."""
    if len(p) < 2:
        return tuple(p)
    return (p[1], p[0]) + tuple(p[2:])


def avoids(word, pats):
    return not any(word_contains(list(word), p) for p in pats)


def rev_set(pats):
    return tuple(reverse_word(p) for p in pats)


def periodic_points(n, pats, restrict_last_eq_first=False):
    """Set of periodic points of s_T on S_n via 3-coloring of the functional graph."""
    perms = list(itertools.permutations(range(1, n + 1)))
    if restrict_last_eq_first:
        perms = [p for p in perms if p[0] == p[-1]]
    f = {p: s_T(p, pats) for p in perms}
    state = {p: 0 for p in perms}  # 0 unknown, 1 on cycle, 2 preperiodic
    for start in perms:
        if state[start] != 0:
            continue
        path = []
        index = {}
        p = start
        while state[p] == 0 and p not in index:
            index[p] = len(path)
            path.append(p)
            p = f[p]
        if p in index:  # found a new cycle
            cyc = index[p]
            for q in path[cyc:]:
                state[q] = 1
            for q in path[:cyc]:
                state[q] = 2
        elif state[p] == 1:
            for q in path:
                state[q] = 2
        else:
            for q in path:
                state[q] = 2
    return {p for p in perms if state[p] == 1}, state, f


def half_decreasing(p):
    """Def 4.2 of arXiv:2008.01164v2. p is 1-based tuple."""
    n = len(p)
    # subsequence p(n-1) p(n-3) ... p(2) for odd n; p(n-1) ... p(3) for even n
    idxs = list(range(n - 2, 0, -2)) if n % 2 == 1 else list(range(n - 2, 1, -2))
    vals = [p[i] for i in idxs]  # idxs are 0-based positions (n-2, n-4, ...)
    return vals == list(range(1, len(idxs) + 1))
