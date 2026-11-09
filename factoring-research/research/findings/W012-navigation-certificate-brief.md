# W012 fixed navigation certificate

One exact instance is selected before evaluation: N=101*211=21311.
The proposed factor-selective rule is to start at a balanced integer-hull
vertex and move only to adjacent vertices with no larger product x*y,
hoping to reach x*y=N without covering the whole hull. The point
(144,148) has product 21312=N+1 and is the candidate false local minimum.
A fixed exact certificate will enumerate the finite lower hull of
(x,ceil(N/x)), x=1,...,N, solely to identify its two true neighbors.
There is no parameter search, replacement instance, timing comparison
or factoring-performance experiment. If it is not a vertex/local trap,
record that failure without searching for a replacement in this check.
The direct enumeration is proof-certificate generation, not a claimed
fast implementation of hull navigation.
