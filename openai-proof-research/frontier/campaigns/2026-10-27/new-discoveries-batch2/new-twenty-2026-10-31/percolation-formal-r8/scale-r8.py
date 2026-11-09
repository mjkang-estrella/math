from pathlib import Path
r=Path(__file__).resolve().parent
p=r/'extend-r8.py';t=p.read_text().replace('target=18561','target=129671').replace('bounds=[5000,13561,14561,18561]','bounds=[5000,13561,14561,18561,129671]')
t=t.replace(' for start in range(lo,hi,100):\n  end=min(start+100,hi);', ''' starts=[]
 cursor=lo
 while cursor<hi:
  stop=cursor;hintcount=0
  while stop<hi and stop-cursor<(100 if lo<18561 else 500):
   nh=len(steps[stop][2])
   if stop>cursor and hintcount+nh>25000 and lo>=18561:break
   hintcount+=nh;stop+=1
  starts.append((cursor,stop));cursor=stop
 for start,end in starts:
  ''')
p.write_text(t)
