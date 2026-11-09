# Total isolation game (Henning-Rall arXiv:2601.03363v1), Conjecture 1:
# if every component of G has order >= 3 then iota_gt(G) <= 2n/3.
# Rule (source p.2): with S the played set, v is playable iff v is adjacent to
# a vertex u that lies in a nontrivial component of G - N(S), or u in S is
# isolated in G - N(S).  N(S) = open neighbourhood.  Dominator starts.
# usage:
#   isogame.py gen OUTFILE NMAX          -- all graphs (up to iso) n<=NMAX, min component order >=3
#   isogame.py solve INFILE OUTFILE START END
#   isogame.py trees OUTFILE NMIN NMAX   -- all free trees, solved directly
import sys, json, itertools

def canon(n, adj):
    # canonical form: refine by degree/iterated neighbour degree multisets, then brute force within cells
    col = [0] * n
    for _ in range(n):
        sig = [(col[v], tuple(sorted(col[u] for u in range(n) if adj[v] >> u & 1))) for v in range(n)]
        keys = sorted(set(sig))
        new = [keys.index(s) for s in sig]
        if len(set(new)) == len(set(col)) and _ > 0:
            col = new
            break
        col = new
    cells = {}
    for v in range(n):
        cells.setdefault(col[v], []).append(v)
    cl = [cells[k] for k in sorted(cells)]
    best = None
    for perms in itertools.product(*[itertools.permutations(c) for c in cl]):
        order = [v for p in perms for v in p]
        pos = {v: i for i, v in enumerate(order)}
        code = 0
        for i, v in enumerate(order):
            for u in order[i + 1:]:
                code = code * 2 + (adj[v] >> u & 1)
        if best is None or code > best:
            best = code
    return best

def components_ok(n, adj):
    seen = 0
    for s in range(n):
        if seen >> s & 1: continue
        comp = 1 << s; frontier = comp
        while frontier:
            nb = 0
            for v in range(n):
                if frontier >> v & 1: nb |= adj[v]
            frontier = nb & ~comp; comp |= nb
        seen |= comp
        if bin(comp).count('1') < 3: return False
    return True

def gen(nmax):
    levels = {1: {canon(1, [0]): [0]}}
    for n in range(2, nmax + 1):
        cur = {}
        for g in levels[n - 1].values():
            for m in range(1 << (n - 1)):
                adj = g[:] + [m]
                adj = [adj[v] | ((m >> v & 1) << (n - 1)) if v < n - 1 else m for v in range(n)]
                c = canon(n, adj)
                if c not in cur: cur[c] = adj
        levels[n] = cur
        print('n', n, 'graphs', len(cur), flush=True)
    out = []
    for n in range(3, nmax + 1):
        for adj in levels[n].values():
            if components_ok(n, adj): out.append((n, adj))
    return out

def solve(n, adj):
    full = (1 << n) - 1
    memo = {}
    def active(s):
        dom = 0
        for i in range(n):
            if s >> i & 1: dom |= adj[i]
        rem = full & ~dom
        a = 0
        for i in range(n):
            if rem >> i & 1 and (adj[i] & rem or s >> i & 1): a |= 1 << i
        return a
    def val(s, turn):
        k = (s << 1) | turn
        if k in memo: return memo[k]
        a = active(s)
        best = None
        for v in range(n):
            if not s >> v & 1 and adj[v] & a:
                x = 1 + val(s | (1 << v), 1 - turn)
                if best is None or (turn == 0 and x < best) or (turn == 1 and x > best): best = x
        if best is None: best = 0
        memo[k] = best
        return best
    return val(0, 0), val(0, 1)

def trees(nmax):
    # free trees via Pruefer codes deduped by canon (fine for n<=11); for larger use rooted generation
    pass

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'gen':
        gs = gen(int(sys.argv[3]))
        with open(sys.argv[2], 'w') as f:
            for n, adj in gs: f.write(json.dumps([n, adj]) + '\n')
        print('written', len(gs))
    elif mode == 'solve':
        lines = open(sys.argv[2]).read().splitlines()
        a, b = int(sys.argv[4]), int(sys.argv[5])
        worst = {}; viol = []; cnt = 0
        with open(sys.argv[3], 'w') as f:
            for line in lines[a:b]:
                n, adj = json.loads(line)
                d, s = solve(n, adj)
                cnt += 1
                f.write(json.dumps([n, adj, d, s]) + '\n')
                r = d / n
                if n not in worst or r > worst[n][0]: worst[n] = (r, d, adj)
                if 3 * d > 2 * n: viol.append((n, adj, d)); print('VIOLATION', n, adj, d, s, flush=True)
        print('solved', cnt, 'violations', len(viol))
        for n in sorted(worst): print(' n', n, 'max D-value', worst[n][1], 'bound', 2 * n / 3)
