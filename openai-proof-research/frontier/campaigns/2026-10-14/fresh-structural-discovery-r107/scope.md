# Frozen full target T174D

Research target, not a theorem assertion or nomination. Frozen before proof development in this directory on 2026-10-19 UTC (environment local date October 18).

There exists an absolute real constant C>0 such that for every integer k>=1, every finite loopless directed multigraph D=(V,A) with |V|>=2, indeg_D(v)=outdeg_D(v) for each vertex, and |delta_D^+(S)|>=k for every nonempty proper subset S of V, and every prescribed root r in V, there is a spanning out-arborescence T rooted at r using arcs of D, such that simultaneously for every S subset V,

 |T intersect delta_D(S)| <= (C/k) |delta_D^+(S)|.

Here arcs are individually labelled, antiparallel arcs are permitted, delta_D(S)=delta_D^+(S) disjoint union delta_D^-(S), and a spanning out-arborescence has indegree zero at r, indegree one elsewhere, and a directed path from r to every vertex. Equivalently its underlying undirected multigraph is a tree with those indegrees. Eulerian balance gives |delta_D(S)|=2|delta_D^+(S)|. The bound is on TOTAL crossing arcs of T, not merely one direction or cuts avoiding r.

C is independent of k, |V|, multiplicity, degree ratios, D and r. This is an existence claim; no algorithmic time claim is included. No additional regularity, planarity, symmetry, bounded size, expansion, large k relative to |V|, or adjustable root restriction is permitted. A logarithmic loss or a union of several trees does not satisfy this target. If unresolved, retain this scope without nominating a weaker result.

Prospective dependencies: source174 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, under all stated source contracts, and classical finite directed graph results as precisely documented after reading. All source truth is stipulated. Proposed unpaid operation: retain directed reachability (or rooted directed cut lower bounds) through simultaneous upper-cut thinning. The source's undirected tree-packing frame alone is not asserted to supply this.
