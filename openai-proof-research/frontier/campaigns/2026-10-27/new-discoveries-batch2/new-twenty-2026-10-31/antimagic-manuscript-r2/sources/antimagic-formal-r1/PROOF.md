# Proved fragments and remaining mathematics

The lane follows the independently reviewed ordinary proof in sibling expanded-corpus-r142/outputs/antimagic/proof.md, with the corrections in sibling antimagic-review-r1/REVIEW.md. Those inputs were read, not edited. Published citations throughout this handoff use Lemmas 2.9 and 2.10 and Conjecture 6.1. The binary n = 2 construction is source Figure 5; the other n = 2 case uses source ingredients.

The core labelling formula uses `N = sum_{1 <= h < n} t^h`, `Z = (N - t)/2 + 1`. The first row is Z followed by N - t + 2 through N. For later internal rows, r = off(h) + i and d = 1 + r/2 give Z - d for even r and Z + d for odd r. The t = 2, h = 2 indices 1 and 3 are transposed. Leaves use the reviewer's displacement permutation and reversed blocks. This is implemented as total natural-number functions. Truncating subtraction is intentional; the hypotheses that make it ordinary subtraction must still be proved in Construction.

The proved shell identity is `(Z-d)+(Z+d)=2Z` when d <= Z. The binary transposition is an involution. Equal translation preserves inequality of labels. These are useful fragments, not substitutes for the missing general bijectivity and range proofs.

The finite colour lemma takes an injective family of leaf weights bounded by m and a vertex of weight greater than m. Inserting the latter into the leaf-colour image increases its cardinality by one; inclusion into the full colour image gives the lower bound. Applying it to actual graph leaves remains part of LowerBound.

For a graph isomorphism e, the map on unordered edge pairs induces an edge equivalence. Precomposing a labelling with its inverse and casting the Fin cardinality transports the labelling. Equivalence reindexing of the finite sum, together with preservation of membership in an unordered pair, proves the weight identity. Surjectivity on vertices gives equality of colour images. Properness and the spectrum then transport in both directions. The degree-preservation theorem gives equality of the number of degree-one vertices, and spectrum equality gives chiLA equality. All these steps are proved in AntimagicIso.

The conditional even_case theorem combines precisely the assumed construction and lower bound using least_of_bounds. The conditional full endpoint first uses the assumed structural bridge, transports the spectrum and leaf count by the proved invariance, substitutes the assumed canonical leaf count, and applies the infimum characterization. No missing proof is disguised as a definition with a chosen inhabitant.

The remaining general mathematical content is substantial: canonical tree structure, incidence correspondence, leaf count and lower bound; the arithmetic construction proofs across all four case families; and uniqueness of arbitrary finite full trees. The six kernel row checks and 42 Python cases do not settle these general obligations.
