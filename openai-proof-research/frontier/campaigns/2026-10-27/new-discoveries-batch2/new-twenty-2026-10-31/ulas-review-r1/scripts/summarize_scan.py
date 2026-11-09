import json, sys
tot_v = tot_cne = 0; rows = []
for l in open(sys.argv[1]):
    if not l.startswith('{'): print(l.strip()[:200]); continue
    r = json.loads(l); tot_v += r['n_violations']; tot_cne += r['n_claimed_but_not_equal']
    if r['n_violations'] or r['n_claimed_but_not_equal'] or r['zero_diffs'] or r['m'] % 4 == 3:
        rows.append((r['m'], r['m'] % 16, r['n_violations'], r['n_claimed_but_not_equal'], len(r['zero_diffs']), r['min_excess'], r.get('sharp_const_guess_max6_v2m1p3'), r['equality_count']))
print("total violations", tot_v, "total claimed-equality failures", tot_cne)
for row in rows:
    m, r16, v, c, z, me, g, ec = row
    flag = "" if (me + 6 == g) else "  <-- min const != max(6,v2(m+1)+3)"
    if r16 == 15 and me < 1: flag += "  <-- m=15 mod 16 EQUALITY FOUND"
    print(f"m={m} m%16={r16} viol={v} claimFail={c} zeros={z} minexcess={me} const={me+6} guess={g} eqcount={ec}{flag}")
