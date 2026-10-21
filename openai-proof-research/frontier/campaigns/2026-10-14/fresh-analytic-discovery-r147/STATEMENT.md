# T360S147 — frozen full statement

Frozen after the feasibility calculation in CHECKPOINT.md and the source/primary/history readings recorded in CHRONOLOGY.md, before author-proof drafting. This is an author nominee, not an independent correctness or contribution grade, acceptance, count, or literature-priority claim.

Let (M,g) be any smooth, connected, compact Riemannian manifold without boundary, of any integer dimension n>=2. No orientability assumption is imposed. Put c(x,y)=d_g(x,y)^2/2 and

I(x)={p in T_xM: d_g(x,exp_x(a p))=a|p|_g for some real a>1}.

Assume weak MTW in precisely this convention: for every x in M, every p in I(x), and every xi,eta in T_xM with <xi,eta>_g=0,

-(3/2) (partial_s^2 partial_t^2) c(exp_x(t xi),exp_x(p+s eta)) at s=t=0 >=0.

There is a finite constant K_g, depending only on the fixed Riemannian manifold (M,g), with the following property. For every pair of real numbers 0<lambda<=Lambda<infinity and every pair of measurable functions rho_0,rho_1:M->R satisfying

integral_M rho_i dvol_g=1 and lambda<=rho_i<=Lambda almost everywhere, i=0,1,

the almost-everywhere unique c-optimal transport map from rho_0 dvol_g to rho_1 dvol_g has a homeomorphic representative T:M->M for which both T and T^{-1} belong to W^{1,1}(M;M), and

integral_M |dT(x)|_HS dvol_g(x) + integral_M |d(T^{-1})(y)|_HS dvol_g(y) <= K_g.

Here W^{1,1}(M;M) means that composition with one (equivalently any) fixed smooth isometric embedding of (M,g) into a finite-dimensional Euclidean space lies in W^{1,1}; |dT|_HS is the intrinsic Hilbert–Schmidt norm of its weak differential. The constant K_g is common to all the displayed density bounds, not merely to each fixed lambda,Lambda class.

The pinned Source360 theorems and operative proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated inputs. No positive separation from the cut locus, nonfocality, strict MTW, density continuity, or bounds on density derivatives are assumed. No W^{1,1+epsilon} endpoint conclusion, global W^{2,1} potential conclusion, smoothness, approximation theorem, or solution of I07/I225/I331 is included.
