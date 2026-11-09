import sys; sys.argv=['x','0']
exec(open('scripts/signed6.py').read().split('t0=time.monotonic()')[0])
# three unbalanced triangles sharing vertex 0
E=[(0,1),(1,2),(0,2),(0,3),(3,4),(0,4),(0,5),(5,6),(0,6)]; neg={1,4,7}
sc=signed_circuits(7,E,neg); print('H circuits',len(sc),[has_cover(9,sc,k) for k in range(1,7)])
# Fan's first example m=1: triangles A=(0,1,2), B=(3,4,5) unbalanced, paths 0-6-7-3 and 1-8-9-4 of length 3 forming unbalanced circuit
E=[(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,6),(6,7),(7,3),(1,8),(8,9),(9,4)]
neg={0,3,6}  # edge(0,1) in A and path, edge (3,4) in B, path edge
sc=signed_circuits(10,E,neg); print('G circuits',len(sc),sorted(set(len(c) for c in sc)),[has_cover(12,sc,k) for k in range(1,7)])
