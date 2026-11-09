# Exact remaining gap; zero credit

The first ordered r4 goal is complete. The bidegree support bounds, reflection with phase 1, unconditional graph representation, and unconditional reduced certificate are complete. The literal `ContactPilot.refutation : ¬ ContactPilot.SourceConjecture` is absent.

## Next required lemma

```lean
 theorem bidisk_contact_six :
   ContactPilot.HasZeroSetContact
     (ContactPilot.eval₂ ContactPilot.bidiskNumerator) (-1) 1 6
```

It must follow from the inherited `half_plane_contact_six : HasHalfPlaneContact R 6`, with explicit uniform constants and actual root localization. None of the new matrix lemmas proves this contact assertion.

For a circle point z near −1 use x = i(1+z)/(1−z), which is real and satisfies |x| = ‖1+z‖/‖1−z‖. The source coordinate is betaInv z = −1/x. For a lower-half-plane pole root u of R x u = 0, the expected numerator root is beta (star u). Prove its numerator-zero identity using the real coefficients of N,Q at real −1/x, the inherited clearing identities, and R_from_quotient. Then establish the quantitative height comparison and neighborhood bounds uniformly. In particular, an upper-bound witness in the half-plane statement must be localized near 0 before its image is claimed to lie near 1. A comparison of imaginary parts alone does not establish that localization. The existing explicit quadratic branches are available for this obligation.

After the transfer, prove contact two excluded from the two-sided comparisons as requested. The already checked `refutation_of_bidisk_contact` then supplies the literal negation once applied to bidisk_contact_six; it currently remains conditional. Add a declaration with the exact required name `ContactPilot.refutation`, repeat strict extracted replay, leanchecker, all-declaration audit and negative controls, update correspondence and submit to root. Only root may accept. Counts remain 21/40 beyond the previous 39.
