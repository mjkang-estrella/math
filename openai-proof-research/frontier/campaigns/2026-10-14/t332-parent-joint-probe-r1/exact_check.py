#!/usr/bin/env python3
"""MIT. Rational finite assignment checker. No global retraction assertion."""
from fractions import Fraction as F
from pathlib import Path
import json,itertools
B=Path(__file__).parent

def check(parent,w,anchors,points,outputs,L):
 d=len(parent);assert len(outputs)==len(points)
 assert d>0 and all(isinstance(p,int) and -1<=p<e for e,p in enumerate(parent))
 assert len(w)==d and all(v>0 for v in w)
 assert all(len(v)==d for v in anchors+points+outputs)
 for q in anchors+outputs:
  assert all(q[e]>=sum(q[f] for f,p in enumerate(parent) if p==e) for e in range(d))
 xs=anchors+points;ys=anchors+outputs
 maxratio=F(0)
 for i,j in itertools.combinations(range(len(xs)),2):
  den=sum(w[e]*abs(xs[i][e]-xs[j][e]) for e in range(d))
  num=sum(w[e]*abs(ys[i][e]-ys[j][e]) for e in range(d))
  assert num<=L*den
  if den:maxratio=max(maxratio,num/den)
 return maxratio

def rational(v):return F(str(v))
def main():
 cases=[json.loads(s) for s in (B/'results.jsonl').read_text().splitlines()]
 structured={r['name']:r for r in map(json.loads,(B/'structured-results.jsonl').read_text().splitlines())}
 for line in (B/'reduced-results.jsonl').read_text().splitlines():
  row=json.loads(line);original=structured[row['name']]
  cases.append({**original,'name':row['name']+'_24points','points':[original['points'][i] for i in row['point_indices']],'result':row['result']})
 report=[]
 for case in cases:
  assert case['result']['status']==0
  parent=case['parent'];d=len(parent);w=list(map(rational,case['weights']))
  anchors=[list(map(rational,x)) for x in case['anchors']];points=[list(map(rational,x)) for x in case['points']]
  outputs=[]
  for q in case['result']['output_flows']:
   y=[max(F(0),rational(x).limit_denominator(10**6)) for x in q]
   # Repair any rational-rounding cone error by upward propagation.
   for e in reversed(range(d)):y[e]=max(y[e],sum(y[f] for f,p in enumerate(parent) if p==e))
   outputs.append(y)
  ratio=check(parent,w,anchors,points,outputs,F(2))
  # A corrupted output is not accepted merely because the optimizer said success.
  bad=[x.copy() for x in outputs];bad[0][-1]=F(-1)
  try:check(parent,w,anchors,points,bad,F(2))
  except AssertionError:pass
  else:raise AssertionError('negative output mutation accepted')
  report.append({'name':case['name'],'anchors':len(anchors),'unknown_points':len(points),'verified_L':'2','exact_max_pair_ratio':str(ratio),'rational_output_flows':[[str(x) for x in y] for y in outputs],'negative_output_control':'rejected'})
 print(json.dumps({'status':'PASS_EXACT_FINITE_ASSIGNMENTS_ONLY','case_count':len(report),'cases':report,'limits':'Each listed finite configuration admits the returned2-Lipschitz assignment. No exact lower optimum, infinite extension, universal retraction, or fullT332 theorem is proved.'},indent=2))
if __name__=='__main__':main()
