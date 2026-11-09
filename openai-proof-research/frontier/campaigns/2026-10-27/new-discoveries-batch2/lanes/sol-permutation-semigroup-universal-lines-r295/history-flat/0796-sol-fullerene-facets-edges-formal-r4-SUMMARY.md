# Real fullerene facets and actual polygon vertices

Implementation verification IN PROGRESS. This document is not a PASS receipt.
Root alone accepts; counts remain 9 additional /39 total /next40. Full-source,
novelty and acceptance HOLD. No literal fullerene instance is asserted.

## Exact interfaces

Namespace FullereneGeometry, FacetsG.lean and FacetsH.lean:

* all_section_dimensions_G/H: every one of the 32 actual facetSection qG/qH i
  has affineDimension 2. affineDimension is mathlib finrank of vectorSpan,
  equivalently the dimension of the direction of affineSpan.
* all_sections_facets_G/H and all_geometric_facets_G/H: the actual indexed
  sections are exactly ALL geometric facets of the actual real polytope.
* facets_standard_equivalence_G/H: GeometricFacet is equivalent to
  MaximalProperFace for these polytopes. The latter quantifies over arbitrary
  convex mathlib IsExtreme faces, without assuming they are exposed.
* section_vertices_G/H: the actual extreme points of a section are exactly
  pG/pH '' incidentG/H i. This identifies extreme points, not only hull generators.
* points_injective_G/H and sections_distinct_G/H: actual listed points and
  actual section sets are pairwise distinct.
* section_vertex_count_G/H: each actual facet has five or six actual vertices,
  according to its explicit checked pentagonIdsG/H membership.
* facet_count_G/H, pentagonal_facet_count_G/H, hexagonal_facet_count_G/H:
  exactly 32 genuine facets, exactly 12 with five vertices and 20 with six.
* literal_polygon_G/H and all_facets_polygons_G/H: every actual facet is a
  compact convex real two-dimensional polygon, finite in its actual extreme
  vertices and equal to their convex hull, with exactly five or six vertices.

GeometricFacet is a literal nonzero REAL linear supporting functional and level,
an upper bound on every real point of P, equality of the face with that supporting
section, nonemptiness, and affine dimension two. It is not a finite incidence
surrogate. PolygonCore.geometricFacet_isExposed additionally supplies the pinned
mathlib IsExposed bridge. ConvexPolygon expresses the usual convex real polygon
as a compact two-dimensional convex hull of its finite actual extreme points;
the vertex count distinguishes pentagons and hexagons. Compact_G/H and the
actual nonempty interior are inherited unchanged, as are the full vertex/hull
theorems.

## Proof mechanism

FaceCore proves that every nonempty proper convex face of a finite halfspace
polytope lies in one defining active section. If no defining plane contains the
whole face, finite averaging gives a face point strict on every inequality.
A small real two-sided feasible perturbation through that point forces every
point of P into the face by mathlib IsExtreme, contradicting properness. This
proves the needed face lemma rather than assuming relative interior or exposure.

FacetDimension uses the supporting plane kernel for the dimension upper bound.
Each of 64 small FacetG/H modules checks three actual incident listed real points
and a nonzero coordinate minor. These points are noncollinear, giving the lower
bound. For any real two-dimensional supporting face, containment in a defining
section plus equal vector-span dimensions forces equality of the supporting
sections. FacetStandard proves equivalence with maximal proper convex faces.

IncidenceCore transports exact checked integer active equations to actual real
dot products through unchanged r3 bindings. The actual extreme-point equality
follows from mathlib IsExtreme.extremePoints_eq and inherited complete_vertices.
The exact finite incidence sets and injective point maps then give the actual
vertex counts and distinctness. Rational computations alone are never used as
the geometry theorem. The inherited triple certificates are not regenerated.

## Residual obligation 3 and scope limits

No edge theorem is claimed in this component. Still required: show each edge is
a genuine one-dimensional convex face/segment with exactly two listed endpoints;
exhaust all such edges for arbitrary real supporting data; prove facet adjacency
iff intersection is a genuine one-dimensional edge; identify it with the exact
original G/H adjacency; and prove every primal vertex has exactly three incident
edges. These are necessary before any literal fullerene instance is claimed.
No matrix exponential, analytic fullSourceClaim, Steinitz/Whitney construction,
source resolution, novelty clearance or discovery credit is asserted.

## Verification and provenance

The mathematical proof modules inherited from r3 are byte-identical. Flat immutable
references freeze the r6 root disposition, r3 sources/archive/harness/receipts,
original rational realizations and consulted mathlib bodies before scientific
reading. Administrative snapshots are not moving scientific premises. Scientific
original/copy hashes are rechecked after work. No external retrieval occurred.

See RUN.md, source.zip, archive-files.json, pins.json, freeze.json,
source-bindings.json, audit.json, owned-declarations.json, replay-receipt.json,
provenance.json, MANIFEST.json and verification-receipt.json. Only completed PASS
receipts establish final verification. Both unsafe and partial are hard-fail
checked for all actual mathematical origins, private/generated declarations and
transitive type/body dependencies. Only propext, Classical.choice and Quot.sound
are allowed. Compiler calls are serial under the original caps. All development
failures remain evidence; FAILURES.md records the index-order correction and the
memory-limited rejected continuity import. Owned compiled objects are removed
before the manifest, and final verification is a separate guarded invocation.
