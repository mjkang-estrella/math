# T008M: reviewer simplification and parent response

This addendum preserves the frozen author candidate and scope. The independent
proof reviewer identified the following simplification as O1. Parent checked
its argument directly; this is a response to that finding, not a second
independent review or a new counted result.

For a single block Phi_T with 1 <= m <= T and b=T-m, take any word w of
weight 1 <= k <= T. Put mprime=min(m,k) and bprime=k-mprime. Then mprime<=m
and 0<=bprime<=b. Cut w at its first letter reaching mprime and write
w=a e_d v. Set r=mprime-wt(a)>=1 and s=bprime-wt(v)>=0. These give original
states P(a,r) and Q(v,s), since their state budgets are mprime and bprime.
The entry between them extracts exactly w: the path must delete a, cross
with the unique letter of weight r+s=d, and create v. It has multiplicity
one. Thus Phi_T is injective on each weight k. Different weights occupy
disjoint level differences; the constant maps to the identity and positive
weights have zero diagonal. Consequently Phi_T is faithful on all A_T.

The single block Phi_N therefore suffices for the full frozen theorem, with
C=K in the candidate's notation. The original three blocks and padding
argument remain valid, but are unnecessary. They must not be presented as
a necessary mechanism or independently credited contribution. The target
and its lower bound and limits are unchanged.

The independent contribution gate is still pending. Any favorable assessment
must consider this finding explicitly; otherwise a fresh review round is
required with the original brief and this response. No contribution verdict,
formal coverage or acceptance is inferred from the proof pass.

Other optional exposition points O2-O7 remain in the anchored proof review.
No frozen author or review file has been edited. Original prose CC BY 4.0.
