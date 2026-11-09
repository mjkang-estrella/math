import itertools, decomp, spider, sys
bad=0; cnt=0
for k in (3,4):
    M = 9 if k==3 else 5
    for legs in itertools.combinations_with_replacement(range(1,M+1),k):
        n,e = decomp.spider_edges(legs)
        g1 = decomp.grundy_original_tree(n,e)
        g2 = spider.spider_value(legs)
        cnt+=1
        if g1!=g2:
            bad+=1; print("MISMATCH",legs,g1,g2)
print(cnt,"checked",bad,"mismatches")
