from pathlib import Path
import random,json
D=Path(__file__).resolve().parents[1];ns={'__file__':str(D/'scripts/partitions.py')};s=(D/'scripts/partitions.py').read_text().split('rows=[]')[0];exec(compile(s,str(D/'scripts/partitions.py'),'exec'),ns);f=ns['ordcols'];rng=random.Random(218);bad=[];count=0;size=0;maxside=0
for i in range(30000):
 h=rng.randrange(2,100);w=rng.randrange(2,100);p=tuple(sorted((rng.randrange(1,w+1) for _ in range(h)),reverse=True));a=f(p);b=f(p[:-1]);count+=1;size=max(size,sum(p));maxside=max(maxside,*p,h)
 if len(b)>len(a) or any(u>v for u,v in zip(b,a)):bad.append({'partition':p,'columns':a,'deleted':b});break
row={'seed':218,'samples':count,'max_size':size,'max_side':maxside,'violations':bad};print(json.dumps(row));(D/'logs/partition-extended-results.json').write_text(json.dumps(row,indent=2))
