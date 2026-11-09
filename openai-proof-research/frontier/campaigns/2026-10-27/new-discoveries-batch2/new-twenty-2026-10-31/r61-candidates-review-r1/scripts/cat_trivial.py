# Literal universal reading fails trivially in range at r=2 on Zhang-Ran-Huang's own caterpillar P^{k,t}.
import sys,json;sys.path.insert(0,sys.argv[1])
from cat_verify import analyse
for leafs in [(1,1,1,1),(2,2,2,2),(1,1,1,1,1)]:
    for r in (1,2):
        d=analyse(leafs,r,brute=True,mubrute=True)
        print(json.dumps({k:d[k] for k in ['leafs','n','r','mu','alpha','Delta','max_centres','centre_nbr_degrees','universal_holds','existential_holds','r_le_mu_half']}))
