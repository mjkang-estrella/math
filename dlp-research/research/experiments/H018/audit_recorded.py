#!/usr/bin/env python3
"""Retained independent saved-data audit, run from the dlp-research directory.

This is verification overhead, not a diagnostic rerun or a fixture search.
It checks recorded equations and exact event identities, not scalar products.
The body below is the independently executed native Sol audit command.
"""
import json
from pathlib import Path
r=json.loads(Path('research/experiments/H018/initial_results.json').read_text())
qs=r['q_candidates']; attempts=r['selection_attempts']; rows=[t for a in attempts for t in a.get('q_tests', [])]
assert len(qs)==39 and qs==sorted(set(qs)) and 8191 not in qs
assert [a['b'] for a in attempts]==[1,2,3,4]
assert attempts[1]=={'b':2,'outcome':'rational_two_torsion_at_minus_one'}
assert [[t['q'] for t in a.get('q_tests', [])] for a in attempts]==[qs,[],qs,qs[:18]]
assert len(rows)==96 and all(not t['is_zero'] and 0<t['multiple_z']<8191 for t in rows)
assert r['events']==sum(r['phase_events'].values())==sum(r['event_categories'].values())==71755
for phase,kinds in r['phase_event_categories'].items():
    assert sum(kinds.values())==r['phase_events'][phase]
for kind,count in r['event_categories'].items():
    assert sum(kinds.get(kind,0) for kinds in r['phase_event_categories'].values())==count
D=sum(t['q'].bit_length()-1 for t in rows)
A=sum(t['q'].bit_count()-1 for t in rows)
L=sum(t['q'].bit_length() for t in rows)
expected={'field_square':8*D+5*A,'field_mul':5*D+15*A,'field_add':3*D+A,'field_sub':7*D+8*A,
          'comparison':2*D+3*A+17*len(rows)+L+len(rows),'bit_and':D,'bit_shift':14*len(rows),
          'integer_add':len(rows),'array_write':len(rows),'trace_field':5*len(rows)}
assert expected==r['phase_event_categories']['order_certification']
assert sum(expected.values())==56920
# Verification ONLY of recorded public point data; no scalar multiplication,
# new points, curve generation, point counting or alternative fixture search.
p=8191
for a in attempts:
    if 'gx' not in a: continue
    x,y,b=a['gx'],a['gy'],a['b']
    assert (y*y-x*x*x-x-b)%p==0 and 0<y<=4095
    for t in a['q_tests']:
        x,y,z=t['multiple_x'],t['multiple_y'],t['multiple_z']
        assert all(0<=v<p for v in (x,y,z))
        assert (y*y-x*x*x-x*z**4-b*z**6)%p==0
assert r['status']=='inconclusive' and r['cap_hit'] is None and r['phase_reservation_overruns']=={}
assert r['controls']==r['features']==[]
assert not r['planted_control_validated'] and not r['controls_completed'] and not r['feature_sampling_completed']
assert not any(k in r for k in ('fixture','primitive_w','primitive_attempts','shared_affine_samples'))
print(json.dumps({'audit':'PASS recorded-data verification only','candidate_count':len(qs),'order_tests':len(rows),
 'tests_by_b':[len(a.get('q_tests',[])) for a in attempts],'ordinary_doubles':D,'ordinary_additions':A,
 'exact_reconciled_order_events':sum(expected.values()),'selection_events':r['phase_events']['selection_setup'],
 'total_events':r['events'],'recorded_point_equations_verified':len(rows)+3,'no_fixture_controls_features':True}))
