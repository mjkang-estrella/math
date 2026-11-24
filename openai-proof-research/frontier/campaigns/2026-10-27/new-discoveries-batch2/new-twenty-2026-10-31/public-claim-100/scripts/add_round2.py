#!/usr/bin/env python3
"""Add or replace one round-2 row in extra-rows.json from a small JSON spec (path as argv[1]).
Spec keys: mathdb_id, status, outcome, note, lean_endpoints, replay_record, submission, row_statement,
row_statement_source, adversarial_verdicts, caveats, sweep_lane, sweep_verdict, queries, routes_refused,
closest {citation, read, url}."""
import json, sys, os
P = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
s = json.load(open(sys.argv[1]))
x = json.load(open(os.path.join(P, 'extra-rows.json')))
x[str(s['mathdb_id'])] = {
    'status': s['status'], 'note': s['note'], 'outcome': s['outcome'],
    'lean_endpoints': s['lean_endpoints'], 'replay_record': s['replay_record'],
    'acceptance_record': s.get('acceptance_record', 'not in ledger (round 2; pipeline complete; see packet)'),
    'submission': s['submission'], 'row_statement': s['row_statement'],
    'row_statement_source': s['row_statement_source'], 'adversarial_verdicts': s['adversarial_verdicts'],
    'caveats': s['caveats'],
    'prior_art': {'sweep_lane': s['sweep_lane'], 'sweep_verdict': s['sweep_verdict'],
                  'queries_and_routes': s.get('queries', 'see lane'), 'routes_refused': s.get('routes_refused', []),
                  'closest_prior_read': s.get('closest')}}
json.dump(x, open(os.path.join(P, 'extra-rows.json'), 'w'), indent=1, ensure_ascii=False)
print('extra rows:', len(x))
