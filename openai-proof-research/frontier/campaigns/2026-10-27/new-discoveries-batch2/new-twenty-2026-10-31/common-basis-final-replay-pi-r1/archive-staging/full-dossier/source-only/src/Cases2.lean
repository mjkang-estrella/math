import Bases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CommonBasis332371
theorem check_20 : baseList.all (fun b => decide (∀ e ∈ ({0,2,5,6} : Finset V) \ b,
    ∃ f ∈ b \ ({0,2,5,6} : Finset V), insert f (({0,2,5,6} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_21 : baseList.all (fun b => decide (∀ e ∈ ({0,2,5,7} : Finset V) \ b,
    ∃ f ∈ b \ ({0,2,5,7} : Finset V), insert f (({0,2,5,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_22 : baseList.all (fun b => decide (∀ e ∈ ({0,2,5,8} : Finset V) \ b,
    ∃ f ∈ b \ ({0,2,5,8} : Finset V), insert f (({0,2,5,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_23 : baseList.all (fun b => decide (∀ e ∈ ({0,3,4,5} : Finset V) \ b,
    ∃ f ∈ b \ ({0,3,4,5} : Finset V), insert f (({0,3,4,5} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_24 : baseList.all (fun b => decide (∀ e ∈ ({0,3,4,6} : Finset V) \ b,
    ∃ f ∈ b \ ({0,3,4,6} : Finset V), insert f (({0,3,4,6} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_25 : baseList.all (fun b => decide (∀ e ∈ ({0,3,4,7} : Finset V) \ b,
    ∃ f ∈ b \ ({0,3,4,7} : Finset V), insert f (({0,3,4,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_26 : baseList.all (fun b => decide (∀ e ∈ ({0,3,4,8} : Finset V) \ b,
    ∃ f ∈ b \ ({0,3,4,8} : Finset V), insert f (({0,3,4,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_27 : baseList.all (fun b => decide (∀ e ∈ ({0,3,5,7} : Finset V) \ b,
    ∃ f ∈ b \ ({0,3,5,7} : Finset V), insert f (({0,3,5,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_28 : baseList.all (fun b => decide (∀ e ∈ ({0,3,6,7} : Finset V) \ b,
    ∃ f ∈ b \ ({0,3,6,7} : Finset V), insert f (({0,3,6,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_29 : baseList.all (fun b => decide (∀ e ∈ ({0,3,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({0,3,7,8} : Finset V), insert f (({0,3,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
end CommonBasis332371
