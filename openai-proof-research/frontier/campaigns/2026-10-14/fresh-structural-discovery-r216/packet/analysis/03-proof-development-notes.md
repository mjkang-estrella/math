# Proof development after the freeze

The frozen target is unchanged. Two clarifications were added while developing the author proof, rather than silently strengthening a source interface:

- The doubling now starts with the exact ACGK birth d_tau=t+(1/4+tau)(D_0−t), continues to tau=1/12 and then uses positive dilation. On reducing to the homogeneous model, positive scaling by 3 gives D=t³−t centrally and background 3t. The radial interpolation therefore has C=3−4B+u a and C′≥−4B′. Its strict Euler estimate is E≥−(8/3)rB′−4C/3>0. This avoids assuming a nonstandard shrinking birth has the canonical natural class.
- The group argument only needs the 2-localization of a to have order 4 or 8. Choose an integral representative with odd generator coordinate after localization. Do not assume an integral element has no odd-primary component merely because the supplied calculation is 2-local.

These clarifications preserve all four conclusions of STATEMENT.md. The original prefreeze computations remain intact in 02-prefreeze-reduction.md.

## Author scrutiny, not independent review

The final proof uses a fixed sufficiently small ACGK birth parameter tau_0 and dilates its two critical values. After removing the compact part of F through regular zero-level partitions, it reduces the dilation and then changes tau to 1/12. This avoids a potentially nonsmooth relabeling at a concatenation point. All actual parameter intervals are compact and choices of A are uniform.

The potentially nonproper exterior translation is used only to normalize zero hypersurfaces to compact partitions. No claim is made that that entire ambient translation extends smoothly across the stereographic point. The endpoint comparison instead uses the local boundary graph b=phi(w_s), with phi=O(|w_s|²), dphi=O(|w_s|), and a relative C^1 cap normalization. This distinction is needed for the infinity argument.

Review-critical interfaces: (i) the use of AIS Proposition 4.4 at the integral stable-class level; (ii) identification of the concrete radial-cutoff continuation with its natural doubled tube; (iii) compact partition normalization and the cap comparison in §3; and (iv) restricting an unmarked natural-coset equality to the fixed S^9 slice. They have been argued in the author proof; this is not an assertion that an independent reviewer has accepted them.

The finite group argument now asserts order 4 or 8 only after 2-localization. All four integral classes are nonetheless distinct. Original prefreeze statements about an integral finite order were not silently propagated to the final proof.
