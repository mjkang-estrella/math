import sys
src=open(sys.path[0]+'/orderable_binary_search.py').read().split('t=time.time()')[0]
sys.argv=['x','3','7','1']; exec(src)
def graphic_vecs(nv,edges):
    return [(1<<a)|(1<<b) for a,b in edges]  # full GF(2) incidence vectors represent M(G)
def test(name,vecs,expect):
    c=circuits(vecs); o=orderable(len(vecs),c); print(name,len(vecs),'elements, circuits',len(c),'orderable',o,'expected',expect,'OK' if o==expect else 'MISMATCH')
F7=[1,2,4,3,5,6,7]
test('F7',F7,False)
# F7* : dual of F7, rank 4: [I4 | A^T] where F7=[I3|A], A columns 3,5,6,7
A=[3,5,6,7]
F7s=[1,2,4,8]+[sum(((A[j]>>i)&1)<<j for j in range(4)) for i in range(3)]
test('F7*',F7s,False)
K4=graphic_vecs(4,[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]); test('M(K4)',K4,True)
K5=graphic_vecs(5,[(a,b) for a in range(5) for b in range(a+1,5)]); test('M(K5)',K5,True)
K33=graphic_vecs(6,[(a,b) for a in range(3) for b in range(3,6)]); test('M(K3,3)',K33,True)
# R10: rank 5, vectors of weight 2 in a 5-dim space over GF(2) with... R10 = all 10 vectors in GF(2)^5 with exactly 3 ones
R10=[v for v in range(32) if bin(v).count('1')==3]; test('R10',R10,False)
P=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(5+i,5+(i+2)%5) for i in range(5)]
test('M(Petersen)',graphic_vecs(10,P),True)
