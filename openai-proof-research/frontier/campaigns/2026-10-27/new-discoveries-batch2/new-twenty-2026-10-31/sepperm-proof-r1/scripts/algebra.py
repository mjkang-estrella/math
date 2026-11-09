# OBSOLETE EXPLORATORY MODEL: incorrect actual-record normalization; see ATTEMPTS.md.
import sympy as s
r,j=s.symbols('r j',integer=True,positive=True)
# normalized by c(r,j); interior 1<=j<=r
x=j*(j+1)/((r-j+1)*(r+j)) # c(r,j-1)/c(r,j)
y=(r+1)*j*(j+1)/((r-j+2)*(r-j+1)*(r+j)) # c(r+1,j-1)/c(r,j)
z=(r+1)*(j-1)*j*j*(j+1)/((r-j+3)*(r-j+2)*(r-j+1)*(r+j)*(r+j-1))
print(s.factor(1+x-y+z))
