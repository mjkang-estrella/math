#!/usr/bin/env python3
"""Build dispositions.json for lane pi-mathdb-primary-qualified-breadth-r349.

Reads the 50 reserved MathDB records IN PLACE from the verified corpus chunks
(pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-*.jsonl).
No corpus bytes are copied; only per-record metadata fields are extracted into
the lane payload.
"""
import json, os, sys

BASE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # lanes/
LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
INV = os.path.join(BASE, "pi-mathdb-full-corpus-inventory-r301")
RES = os.path.join(BASE, "root-mathdb-breadth-intake-r348", "reserved-ids.json")

EVIDENCE = "cached_full_statement_read"

# mathdb_id -> (disposition, note)
REVIEWS = {
 401252: ("not_pursued", "Deep C*-algebra program (inner conjugacy of diagonal MASAs for localized automorphisms of purely infinite simple graph C*-algebras); no small exact certificate identified."),
 401379: ("not_pursued", "Full characterization of SPN graphs; extensive literature, open core; no bounded full-scope route."),
 401462: ("not_pursued", "Necessity of a complementarity condition for optimal control governed by a variational inequality; specialized analysis, no tractable full-scope mechanism."),
 401608: ("not_pursued", "Explicit cyclic descents AND explicit cyclic action for arbitrary non-ribbon SYT; suspected Adin-Gessel-Reiner-line partial results (existence, non-explicit) not verified here; no bounded route to the explicit description."),
 401609: ("not_pursued", "Same family as 401608 (explicit cyclic descent set only); not pursued."),
 401613: ("not_pursued", "Distribution of Lebesgue shares of Brownian first-visit cells on S^1; no exact mechanism."),
 401875: ("not_pursued", "Vanishing powers of the tautological class eta on strata of differentials; needs new algebraic-geometry input; no small counterexample/proof route."),
 401929: ("not_pursued", "Strongly polynomial quickest-transshipment horizon without parametric search; algorithmic; suspected recent progress unverified."),
 401939: ("not_pursued", "Integrality gap of natural LP for Linear k-Cut; algorithmic extremal; no bounded route."),
 401952: ("not_pursued", "R(T_cw,2^{boxtimes 2}) = 16? Natural decisive calculation is a Koszul-flattening rank >= 16 certificate, but its design is research-heavy and post-2018 literature possible; deferred."),
 401989: ("not_pursued", "Hadwiger covering conjecture; famous and hard."),
 402015: ("not_pursued", "Orthogonal-representation dimension vs chromatic number for G(n,1/2); hard; no route."),
 402067: ("not_pursued", "Exact A_2(11,4) in {129,...,132}; determination needs a large exact packing/clique search far beyond the 512MiB/210s caps; possible finite-geometry literature; deferred."),
 402078: ("not_pursued", "Linear constituents of restrictions to Sylow subgroups of S_n; programmatic representation theory."),
 402087: ("not_pursued", "Explicit character bounds for finite almost quasisimple groups; deep finite group theory."),
 402114: ("not_pursued", "Rational exponents conjecture ex(n,H)=Theta(n^r) for every rational r in (1,2); famous and hard."),
 402126: ("not_pursued", "Distinct degrees in induced subgraphs of Ramsey graphs; famous and hard."),
 402132: ("not_pursued", "Asymptotics of triangle-count logarithmic tail probabilities in G(n,p); hard large deviations."),
 402134: ("not_pursued", "Inducibility of paths P_k for all k>=4; flag-algebra scale; possible literature; deferred."),
 402335: ("not_pursued", "Velocity-robust pressure error estimates for Stokes discretizations; technical FEM analysis; no route."),
 402435: ("publicly_resolved_reported", "Killip-Laurens-Visan, 'Sharp well-posedness for the Benjamin-Ono equation' (arXiv:2304.00124; Inventiones mathematicae 2024): well-posed in H^s, s > -1/2, on line and circle - covers the asked range -1/2 < s < 0. Abstract-level reported; PDF retained at sources/killip-laurens-visan-2304.00124-benjamin-ono-sharp-wellposedness.pdf; proof body NOT read."),
 402614: ("not_pursued", "Brown-Erdos-Sos conjecture f_3(n,e+3,e)=o(n^2); famous and hard."),
 402628: ("not_pursued", "Max degree >= sqrt(|S|) in induced subgraphs of Cayley graphs of Z_2^n on > 2^{n-1} vertices; density/averaging review found no general mechanism; plausible but open; deferred."),
 402630: ("publicly_resolved_reported", "arXiv:2008.06577 (Bucic-Letzter-Sudakov-type): c(l)=1 iff l not divisible by 4; arXiv:2608.06238 'Maximizing directed cycles in tournaments': resolves the remaining l divisible by 4 (carousel tournament). Abstract-level reported; PDFs retained; proof bodies NOT read."),
 402631: ("not_pursued", "Explicit bounded-degree bipartite graph |A|=n^3, |B|=n^2 where every n-subset of A has a perfect matching to B; degree-2/3 hypergraph-design reformulations found in review give no bounded route; deferred."),
 402650: ("not_pursued", "Phase diagram for quasilocality of 1D random walk in random scenery; hard."),
 402655: ("not_pursued", "Precise universal normal-dilation constant C_d; specialized operator theory; possible literature; deferred."),
 402788: ("not_pursued", "Radial Fourier uniqueness on integer-radius spheres; suspected recent Fourier-interpolation literature unverified; deferred."),
 402804: ("not_pursued", "Finite-dimensionality of completed Jacobi algebras of (Q(l),W): l=1 case is elementary (finite iff dW != 0) but the general 'precisely when' classification has no full-scope route."),
 402822: ("not_pursued", "Extremal number of fixed-length distinct-distance chains; possible recent literature; deferred."),
 402838: ("not_pursued", "Hereditary polychromatic colorings: does m_2^*=3 imply m_3^* finite?; no concrete mechanism identified."),
 402897: ("not_pursued", "Benjamini-Schramm Conjecture 1 for planar graphs of minimum degree >= 7; hard percolation."),
 403254: ("not_pursued", "Max primes in intervals y <= (1-eps) log x vs S(y); hard analytic number theory."),
 403281: ("not_pursued", "Tangent cones at Dirac masses in singular Monge-Ampere examples; hard PDE."),
 403559: ("publicly_resolved_reported", "Janzer, 'Rainbow Turan number of even cycles, repeated patterns and blow-ups of cycles' (arXiv:2006.01062; Israel J. Math. 2023): ex*(n,C_2k) = O(n^{1+1/k}), tight against the Bose-Chowla-type lower bound, establishing Theta. Abstract-level reported; PDF retained; proof body NOT read."),
 403562: ("not_pursued", "Rainbow Turan threshold for subdivisions of a clique; adjacent literature exists but not separately verified; deferred."),
 403566: ("not_pursued", "Bollobas-Erdos-Tuza conjecture h(G)=o(n) when alpha(G)=Omega(n); open research problem."),
 403601: ("not_pursued", "Hyperbolicity of all Jensen polynomials of Xi is equivalent to RH; out of scope."),
 403609: ("not_pursued", "Decidability of linear information inequalities; suspected recent literature unverified; deferred."),
 403656: ("not_pursued", "Kissing number tau_3 for regular tetrahedra = 20?; geometric optimization without a bounded exact route; deferred."),
 403684: ("not_pursued", "Tuza's conjecture on weak saturation of hypergraphs; research extremal hypergraphs."),
 403710: ("not_pursued", "Stable reductive Borel-Serre models and the plus-construction; deep algebraic K-theory."),
 403732: ("not_pursued", "Volume measure for LQG in the matter phase (1,25); hard."),
 403778: ("not_pursued", "Fractal pointwise convergence of Schrodinger flows; hard harmonic analysis."),
 403934: ("not_pursued", "'Find a recursive formula' for SSL/ML/dual-ML degree sequences; fuzzy scope; dual ML sequence likely treated in recent ML-degree literature; deferred."),
 403947: ("not_pursued", "D-finiteness of the 1324-avoiding permutation generating function; famous open."),
 403960: ("not_pursued", "GF of Av(3412,52341,635241): needs the OWR catalytic specification (ems.press report not retrieved here); solving the catalytic system exceeds caps; deferred."),
 404008: ("not_pursued", "Largest product-free subsets of A_n; research-level; possible literature; deferred."),
 404025: ("not_pursued", "Linear upper bound conjecture for rainbow matchings f(r,t) <= c(r) t; suspected recent resolution unverified; deferred."),
 404067: ("proposed", "PROPOSED (sole brief): exact tangent-cone characterization of singleton Gram spectrahedra of sums of squares of quadratics; new unconditional upper bound m(n) <= N - w1(n); m(2)=1 and m(3)=2. See proposals.json."),
}

def main():
    reserved = json.load(open(RES))["ids"]
    assert len(reserved) == 50 and len(set(reserved)) == 50
    want = set(reserved)
    recs = {}
    for i in range(1, 21):
        p = os.path.join(INV, "corpus", f"mathdb-normalized-chunk-{i:04d}.jsonl")
        with open(p) as f:
            for line in f:
                r = json.loads(line)
                mid = r["mathdb_id"]
                if mid in want and mid not in recs:
                    recs[mid] = (i, r)
    missing = want - set(recs)
    assert not missing, f"missing reserved ids: {sorted(missing)}"
    out = []
    for mid in sorted(want):
        chunk, r = recs[mid]
        disp, note = REVIEWS[mid]
        out.append({
            "mathdb_id": mid,
            "title": r["title"],
            "canonical_url": r["canonical_url"],
            "post_type": r["post_type"],
            "status": r["status"],
            "solution_count": r["solution_count"],
            "statement_completeness": r["statement_completeness"],
            "source_name": r["source_name"],
            "source_url": r["source_url"],
            "corpus_ref": f"pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-{chunk:04d}.jsonl",
            "evidence_level": EVIDENCE,
            "disposition": disp,
            "note": note,
        })
    assert len(out) == 50
    import collections
    c = collections.Counter(o["disposition"] for o in out)
    print("dispositions:", dict(c))
    with open(os.path.join(LANE, "dispositions.json"), "w") as f:
        json.dump(out, f, indent=1)
        f.write("\n")

if __name__ == "__main__":
    main()
