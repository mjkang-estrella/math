# Full proof outline

For every natural r and every pair of natural exponents i,j, the coefficient of t^i a^j in the exact Fill--Janson polynomial h(t,a;r) is nonnegative.

Write x=1+at and A=(x+3t)(x+2t), B=(x+t)(x+4t), C=(x+t)(x+2t), D=x(x+3t), K=8t^4(x+2t). The homogeneous expression H_n=(x+2t)A^n-(x+4t)B^n+(x+2t)C^n-xD^n has auxiliary sequences U_n=H_(n+1)-DH_n and V_n=U_(n+1)-CU_n. Initial values H_0=U_0=0,V_0=K and recurrence V_(n+1)=BV_n+KA^(n+1), together with H_(n+1)=DH_n+U_n and U_(n+1)=CU_n+V_n, prove simultaneous coefficientwise positivity by induction. The source substitution is proved algebraically in Lean.

All algebra, finite membership tests, and source bridges are proved in the module. See `main.tex` for the detailed argument.
