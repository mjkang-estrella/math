import pathlib
D=pathlib.Path(__file__).resolve().parents[1];p=D/'scripts/paths-random.py';s=p.read_text();fn=(D/'scripts/paths.py').read_text().split('for N in range')[0]
s='import pathlib\n'+fn+'\n'+s
s=s.replace('count=tries=over=0','count=tries=over=qual=0')
s=s.replace('mx=max(mx,p[-1]);over+=p[-1]>bound','mx=max(mx,p[-1]);over+=p[-1]>bound\n  if p[-1]>bound and threeconn(N,E):\n   qual+=1;print("WITNESS",N,p[-1],E,flush=True)')
s=s.replace("'overbound_needing_connectivity_check':over","'overbound_checked':over,'three_edge_connected_violations':qual")
p.write_text(s)
