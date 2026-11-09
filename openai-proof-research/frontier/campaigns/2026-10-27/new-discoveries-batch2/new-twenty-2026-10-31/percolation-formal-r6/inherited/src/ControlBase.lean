import Plane5
namespace Percolation
def maskSet (m : Nat) : Infection 5 := fun p => m.testBit p.val
end Percolation
