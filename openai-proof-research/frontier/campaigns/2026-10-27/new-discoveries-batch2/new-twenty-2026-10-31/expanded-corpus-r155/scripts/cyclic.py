import re,json,pathlib,fractions,random,time
L=pathlib.Path(__file__).resolve().parents[1];s=(L/'sources/344050.txt').read_text();rows=[]
# Recover literal printed witnesses, never treating them as discoveries.
for match in re.finditer(r'π(\d+)\s*=\s*\(([^)]*)\)',s):
 n=int(match[1]);a=[int(x) for x in re.findall(r'\d+',match[2])]
 if len(a)!=n:continue
 total=sum((fractions.Fraction(1,u*u-v*v) for u,v in zip(a,a[1:]+a[:1])),fractions.Fraction())
 rows.append({'n':n,'permutation':a,'sum':str(total),'is_permutation':sorted(a)==list(range(1,n+1))})
# A necessary congruence sieve for n=28: if p>n, at most two incident
# edges have denominators divisible by p, and their scaled residues must cancel.
# This is only a diagnostic on a restricted constructive route.
extensions=[]
for r in rows:
 a=r['permutation'];n=len(a);b=n+1;c=n+2
 for j,(u,v) in enumerate(zip(a,a[1:]+a[:1])):
  if u*u+b*b==v*v+c*c or u*u+c*c==v*v+b*b:
   for middle in ([b,c],[c,b]):
    t=a[:j+1]+middle+a[j+1:]
    total=sum((fractions.Fraction(1,x*x-y*y) for x,y in zip(t,t[1:]+t[:1])),fractions.Fraction())
    if not total:extensions.append({'from_n':n,'to_n':n+2,'permutation':t})
print(json.dumps({'printed_witness_checks':rows,'four_cycle_extensions':extensions,'coverage':'Only printed n=12..27 source witnesses and every adjacent-edge insertion of the next two integers; not an exhaustive nonexistence search.'}))
