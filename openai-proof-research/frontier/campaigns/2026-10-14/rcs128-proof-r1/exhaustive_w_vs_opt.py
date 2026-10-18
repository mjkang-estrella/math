# Independent reviewer exhaustive bounded search (rcs128-proof-r1). SPDX-License-Identifier: MIT
"""Exhaustive: all single words up to length n1 and all unordered pairs of words up
to length n2 over each listed involution; checks W>=OPT_RC (necessary condition).
Finite diagnostics only."""
import itertools, json, sys
from rc_counts import counts, opt_rc
INV = [{'a':'a','b':'b'},{'a':'b','b':'a'},{'a':'a','b':'b','c':'c'},{'a':'b','b':'a','c':'c'}]
def words_upto(alpha, n):
    for L in range(1, n+1):
        for t in itertools.product(alpha, repeat=L):
            yield ''.join(t)
def main(n1, n2, n3):
    tot=0; worst=None
    for cm in INV:
        alpha=sorted(cm)
        if len(alpha)==3: a1,a2,a3=n1-3,n2-2,n3-1
        else: a1,a2,a3=n1,n2,n3
        ws=list(words_upto(alpha,a1))
        fam=[(w,) for w in ws]
        ws2=list(words_upto(alpha,a2))
        fam+=list(itertools.combinations(ws2,2))
        ws3=list(words_upto(alpha,a3))
        fam+=list(itertools.combinations(ws3,3))
        for f in fam:
            c=counts(list(f),cm,'broad'); o,T=opt_rc(list(f),cm); tot+=1
            if c['W']<o:
                print(json.dumps(dict(kind='W_LT_OPT',words=f,cm=cm,W=c['W'],opt=o)));return 1
            if worst is None or c['W']-o<worst[0]: worst=(c['W']-o,f,cm)
    print(json.dumps(dict(families=tot,min_gap=worst[0],witness=[worst[1],worst[2]],bounds=[n1,n2,n3])));return 0
if __name__=='__main__': sys.exit(main(*map(int,sys.argv[1:4])))
