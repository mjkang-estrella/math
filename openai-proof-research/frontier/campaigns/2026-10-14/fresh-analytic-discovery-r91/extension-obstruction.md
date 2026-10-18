# Why a dense polynomial domain does not identify bounded algebras

This is a deterministic operator example, not a QFT counterexample and not a nominee.

On H=ell2(N_0), let D=c00 and define the real Jacobi operator T by

    (Tu)_0=u_1,
    (Tu)_n=4^(n−1)u_(n−1)+4^n u_(n+1), n>=1.

It is symmetric on D. A solution of T* u=i u satisfies u_1=i u_0 and
u_(n+1)=i4^(−n)u_n−u_(n−1)/4. Set v_n=2^n u_n. Then

    v_(n+1)=2i4^(−n)v_n−v_(n−1).

The transfer matrix is [[2i4^(−n),−1],[1,0]], a unitary matrix [[0,−1],[1,0]] plus an error of norm2*4^(−n). The product of its operator norm bounds is at most product_(n>=1)(1+2*4^(−n))<=exp(2/3). Therefore |v_n| is uniformly bounded for every initial pair, and u lies in ell2. The left endpoint fixes the solution from u_0, so dim ker(T*−i)=1. Complex conjugation gives dim ker(T*+i)=1. The closed minimal Jacobi operator has deficiency indices(1,1) and hence a circle of distinct self-adjoint extensions T_theta.

Every extension agrees on D, and e0 is cyclic under its polynomial action: the recurrence expresses e_(n+1) as a polynomial in T_theta applied to e0 after lower basis vectors are removed. All polynomial vacuum moments and all finite polynomial vectors are therefore identical for the extensions. Each T_theta is affiliated with its spectral algebra M_theta=W*(T_theta).

The algebras M_theta cannot all coincide. If two did, cyclicity of e0 makes this abelian algebra a multiplicity-one multiplication algebra with e0 represented by a nonzero-a.e. function. Both affiliated operators are real multiplication functions, and T_theta e0=T_phi e0 forces those functions equal almost everywhere; hence the two self-adjoint operators would be equal, contradiction. Thus distinct choices yield different bounded spectral algebras despite the identical dense polynomial data.

Consequences for the proposed QFT argument: density and agreement of affiliated field insertions on the physical word domain do not imply equality of closed realizations, covariance of spectral projections, or equality of bounded localization algebras. A graph-core argument or genuinely bounded-algebra argument is still necessary. This example satisfies no spacetime/locality/scale axioms and is not evidence that the full r91 target is false.
