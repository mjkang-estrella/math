from fractions import Fraction as F
from pathlib import Path
import json,time
D=Path(__file__).resolve().parents[1];start=time.monotonic();p={(0,0,0):F(1)};out=[]
for a in range(1,81):
 total=0;maximum=F(0);arg=None;fail=[]
 for b in range(a+1):
  for c in range(b+1):
   board=(a,b,c);s=F(0)
   for i,row in enumerate(board):
    for j in range(row):
     nxt=board[:i]+tuple(min(x,j)for x in board[i:]);s+=1-p[nxt]
   val=s/(a+b+c);p[board]=val
   if b and a>1:
    total+=1
    if val>maximum:maximum=val;arg=board
    if val>=F(1,2):fail.append([board,str(val)])
 r=dict(max_row=a,boards_this_row=total,total_states=len(p),maximum=str(maximum),arg=arg,failures=fail);out.append(r);print(r,flush=True);(D/'outputs/chomp-three.json').write_text(json.dumps(out,indent=2)+'\n')
 if time.monotonic()-start>105:break
