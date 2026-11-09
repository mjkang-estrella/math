import MaskRUP
import InputLink
namespace Percolation.MaskRUP
theorem encode_cnf (v : Nat → Bool) (c : CNF.NClause) :
    Holds v (encode c) ↔ CNF.Holds v c := encode_holds v c
end Percolation.MaskRUP
