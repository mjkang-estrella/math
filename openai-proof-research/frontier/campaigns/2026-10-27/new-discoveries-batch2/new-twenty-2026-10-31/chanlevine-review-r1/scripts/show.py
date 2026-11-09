import sys, json
for l in sys.stdin:
    if l.startswith('{'):
        d = json.loads(l)
        print(d['n'], d['m'], d['states'], d['terminal_sccs'], d['unique_component_per_weight'], d['nontrivial_nonterminal_sccs'], d['terminal_min_entry'], d['r'], d['cpu_s'])
    else:
        print(l.strip())
