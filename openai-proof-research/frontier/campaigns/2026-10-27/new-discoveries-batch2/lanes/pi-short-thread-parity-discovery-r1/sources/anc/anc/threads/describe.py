"""Describe pieces: skeleton (branch vertices), threads with lengths, internal/leaf type.
Input lines containing 'P n edges' (possibly prefixed by solver output)."""
import sys
def describe(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E: adj[u].append(v); adj[v].append(u)
    deg = [len(a) for a in adj]
    br = [v for v in range(n) if deg[v] >= 3]
    name = {v: "B%d" % i for i, v in enumerate(br)}
    threads = []
    seen = set()
    for s in range(n):
        if deg[s] == 2: continue
        for nb in adj[s]:
            if (s, nb) in seen: continue
            L = 1; prev = s; cur = nb
            while deg[cur] == 2:
                nxt = adj[cur][0] if adj[cur][0] != prev else adj[cur][1]
                prev, cur = cur, nxt; L += 1
            seen.add((cur, prev))
            a = name.get(s, "leaf"); b = name.get(cur, "leaf")
            threads.append((a, b, L))
    internal3 = sum(1 for a, b, L in threads if L == 3 and a != "leaf" and b != "leaf")
    leaf3 = sum(1 for a, b, L in threads if L == 3 and (a == "leaf" or b == "leaf"))
    desc = " ".join("%s-%s:%d" % t for t in sorted(threads, key=lambda t: (t[0] == 'leaf', t[0], t[1])) if not (t[0] == 'leaf' and t[1] != 'leaf'))
    return len(br), internal3, leaf3, desc
for line in sys.stdin:
    t = line.split()
    if 'P' not in t: continue
    pre = t[:t.index('P')]; t = t[t.index('P'):]
    n = int(t[1]); E = [(int(t[2 + 2 * i]), int(t[3 + 2 * i])) for i in range(n - 1)]
    k, i3, l3, d = describe(n, E)
    print(" ".join(pre), "| branch=%d int3=%d leaf3=%d |" % (k, i3, l3), d)
