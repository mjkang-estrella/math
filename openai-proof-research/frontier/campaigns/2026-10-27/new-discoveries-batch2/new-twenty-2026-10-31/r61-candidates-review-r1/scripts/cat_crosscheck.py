import sys,json
sys.path.insert(0,sys.argv[1])
from cat_verify import analyse
for a,r in [((1,4,6,5,0,6),5),((3,4,5,4,1,5),6),((4,7,6,0,7),5),((6,7,6,0,7),5)]:
    d=analyse(a,r,brute=True,mubrute=False)
    print(json.dumps({k:d[k] for k in ['leafs','n','r','alpha','mu','Delta','max_star','max_centres','centre_nbr_degrees','universal_holds','existential_holds','r_le_mu_half']}),flush=True)
