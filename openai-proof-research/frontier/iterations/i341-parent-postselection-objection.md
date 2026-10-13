# I341 parent objection — postselected channel simulation

2026-10-13. Additional contribution objection; the frozen I341 proposal is unchanged. No acceptance or count change. I342 has been notified while active and must assess this independently.

For a trace-preserving channel Phi:Mat(d)->Mat(e), its normalized Choi state rho=J(Phi)/d and a normalized Bell effect on an input C and the reference half A of rho satisfy, with consistent fixed bases,

    <Omega_d/sqrt(d)|_(C,A) [X_C tensor rho_AB]
         |Omega_d/sqrt(d)>_(C,A) = Phi(X)/d^2.

This identity is a direct matrix-unit contraction, valid also with an arbitrary spectator entangled with C. For a CPTP Phi the selected outcome has probability 1/d^2 independent of the input and spectator. The Stinespring version uses a purification of rho, and its selected branch is the channel isometry divided by d. Thus it reproduces the actual channel environment up to an isometry on Eve.

The input and reference halves of the Bell measurement are both at the sender, and the output half is pre-shared at the receiver. Hence this is an LOCC simulation with postselection, not deterministic teleportation simulation and not a claim of covariance. On success it realizes the full channel, with its environment. If a protocol chooses channel dimensions adaptively, each fixed public branch has a known positive product of selected-outcome weights. Those weights can change the public transcript distribution when all successes are conditioned on, so simply postselecting the entire run does NOT automatically reproduce the original unconditional output. That issue must be paid rather than hidden.

There are two possible exact repairs. First, for a finite bounded-depth, finite-outcome adaptive decision tree, append local classical rejection on each terminal successful branch so its total simulation acceptance probability is a common p_* >0, no larger than the minimum of all branchwise success products. This restores the entire original transcript law and quantum output after conditioning on acceptance. An unused channel resource can be locally discarded; finite tensor products of every potentially needed Choi state remain in C. All rejection coins and Bell outcomes are public. Second, a direct branchwise C proof followed by I341's public-weight argument avoids equality of unconditional transcript laws altogether. Either repair preserves arbitrary correlated memories and bidirectional channel choices.

For PPT-composite Phi, source Choi transfer gives rho in C. Finite resource tensors and every successful local filter preserve C; the transcript-weight correction is a local filter. With the first repair, the normalized successful state exactly implements the desired original code, including an Eve purification up to isometry and extra public success records. Even without invoking the source theorem for a trace-decreasing completed protocol, one can condition on each complete record and apply its n=1 C gap, then combine records as in I341. The second repair gives that same conclusion directly.

This suggests that the full adaptive obstruction may be a standard postselected-Choi consequence of the source's filter-stable uniform zero-key property. It does not apply to an arbitrary zero-K_D Choi state, because ordinary asymptotic zero key alone need not imply a uniform gap under exponentially unlikely filters. It also does not establish a deterministic simulation from C resources. The distinction is central to evaluating how much new content I341 adds.

Primary comparison obligations remain: actual postselected teleportation/channel-state simulation and the source's C filter closure. The displayed identity and equalization argument here are parent derivations, not a claim of a completed literature audit. I342 will determine whether a substantive obstruction survives them.
