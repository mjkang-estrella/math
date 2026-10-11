# Retained exploratory selector failure

The first terminal-only minor calculation used
`r1=next(x for x in states[7]['X'] if not x[xe.index((13,14))])`.
At k=8 the sorted first packing is Z, which also omits T1T2.
Thus r1=Z, `Z-r1=0`, and the proposed list has rank 6 rather than 7.
The missing direction is the pq coordinate: all the other proposed
differences vanish there. At k=6 that same order-dependent selector happens
to select the intended packing. This is a certificate-selection failure,
not a counterexample to the rank theorem. No assertion or exception occurred;
the stdout values were k6 rank5 and k8 rank6, and stderr was empty.

The corrected selector additionally requires pq omitted. The final
construction avoids ordering entirely and defines R1 by its deleted edges.
The full failed calculation is retained in `exploratory-selector.py.disabled`.
