# SOUP recovery: path tightness is paid, identification is not

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Supporting deduction only, counted=false.

Fix beta>1. Set epsilon=n^(-2/3) and f=n^(-1/6)(F-EF). The rescaled stationary OU vector X has generator epsilon(Delta-x·grad), hence

    ||grad f||² <= n^(-1/3) beta²(n-1)/2.

For 0<=s<t<=T, Ito's formula gives a forward martingale increment M with
f(X_t)-f(X_s)=M+integral_s^t epsilon Lf(X_u)du. Apply the same formula to the stationary reversed OU process on [0,T], which has the identical generator. Its backward martingale increment B satisfies f(X_s)-f(X_t)=B+integral_s^t epsilon Lf(X_u)du. Consequently

    f(X_t)-f(X_s)=(M-B)/2.

Both martingale increments have quadratic variation bounded deterministically by

    v=beta²(1-1/n)|t-s|.

The exponential martingale inequality (apply exp(lambda M-lambda²<M>/2), then optimize lambda) gives P(|M|>u)<=2 exp(-u²/(2v)), and the same for B. A union bound, requiring no independence, gives

    P(|f(X_t)-f(X_s)|>u) <= 4 exp[-u²/(2 beta² |t-s|)].

Thus every fixed p>0 has E|Z_n(t)-Z_n(s)|^p<=C_p beta^p |t-s|^(p/2), uniformly n. Smooth F has bounded gradient, so all Ito/martingale operations are legitimate by localization; the deterministic quadratic-variation bound removes localization. Stationarity treats arbitrary finite intervals in R.

Source thm:moments gives sup_n E exp(c|Y_n|)<infinity for the completed fluctuation Y_n=f(g)+n^(-1/6)zeta. Conditional Jensen over the independent centered zeta yields the same bound for f(g). It supplies tightness of Z_n(0). Taking p>2 in the increment estimate proves tightness on each C([-T,T]), and a diagonal compact-set construction proves tightness in C(R) with compact-uniform topology. Every subsequence has a further weakly convergent subsequence.

Every subsequential law is stationary and reversible because those identities hold at finite n and finite evaluation maps are continuous. Its one-point marginal is sqrt(a2(beta))*nu_beta by source thm:main, thm:moments and removal of completion. Its mean is zero. The source exponential bound and Holder imply uniform integrability of every fixed polynomial in finitely many evaluations, so the relevant moments pass along any convergent subsequence.

This does NOT prove full-sequence uniqueness or temporal nonconstancy. A constant-in-time random process with the stipulated nondegenerate one-point law satisfies all conclusions of this note.
