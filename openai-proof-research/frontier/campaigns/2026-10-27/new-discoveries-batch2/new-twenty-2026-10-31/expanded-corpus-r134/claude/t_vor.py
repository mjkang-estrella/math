import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import random, itertools, sys
from vor import *
random.seed(1)
for trial in range(40):
    n = random.randint(1,5); k = random.randint(2,7)
    pos = [random.randrange(1<<n) for _ in range(k)]
    i = random.randrange(k)
    assert scores(n,pos,i) == brute_scores(n,pos,i), (n,pos,i)
print("crosscheck ok")
def count(n,k):
    V=1<<n; c=0
    for rest in itertools.combinations_with_replacement(range(V),k-1):
        pos=(0,)+rest
        if is_equilibrium(n,list(pos))[0]: c+=1
    return c
for n,k in [(3,5),(3,6),(3,7),(3,8),(4,5),(4,6)]:
    print(n,k,count(n,k),flush=True)
