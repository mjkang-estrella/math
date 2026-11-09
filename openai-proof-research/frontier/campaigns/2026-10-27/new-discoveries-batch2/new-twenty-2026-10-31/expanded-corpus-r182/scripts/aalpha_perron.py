# First-order explanation for 351804: Perron right/left vectors of A(G*) and products x_j y_j.
m=4; arcs=[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0)]
A=[[1.0 if (i,j) in arcs else 0.0 for j in range(m)] for i in range(m)]
def pw(M):
    x=[1.0]*m
    for _ in range(20000):
        y=[sum(M[i][j]*x[j] for j in range(m))+x[i] for i in range(m)]  # shift by I for primitivity
        s=sum(y); x=[v/s for v in y]
    lam=sum(sum(M[i][j]*x[j] for j in range(m)) for i in range(m))/sum(x)
    return lam,x
r,x=pw(A); At=[[A[j][i] for j in range(m)] for i in range(m)]; _,y=pw(At)
print('rho(A(G*)) =',round(r,6)); print('right Perron x =',[round(v,4) for v in x]); print('left Perron y =',[round(v,4) for v in y])
print('x_j*y_j =',[round(x[j]*y[j],4) for j in range(m)],' (vertex 1 = max outdegree; vertex 0 has larger product)')
