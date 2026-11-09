import Bases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CommonBasis332371
theorem check_30 : baseList.all (fun b => decide (∀ e ∈ ({0,4,5,6} : Finset V) \ b,
    ∃ f ∈ b \ ({0,4,5,6} : Finset V), insert f (({0,4,5,6} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_31 : baseList.all (fun b => decide (∀ e ∈ ({0,4,5,8} : Finset V) \ b,
    ∃ f ∈ b \ ({0,4,5,8} : Finset V), insert f (({0,4,5,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_32 : baseList.all (fun b => decide (∀ e ∈ ({0,4,6,7} : Finset V) \ b,
    ∃ f ∈ b \ ({0,4,6,7} : Finset V), insert f (({0,4,6,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_33 : baseList.all (fun b => decide (∀ e ∈ ({0,4,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({0,4,7,8} : Finset V), insert f (({0,4,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_34 : baseList.all (fun b => decide (∀ e ∈ ({0,5,6,7} : Finset V) \ b,
    ∃ f ∈ b \ ({0,5,6,7} : Finset V), insert f (({0,5,6,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_35 : baseList.all (fun b => decide (∀ e ∈ ({0,5,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({0,5,7,8} : Finset V), insert f (({0,5,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_36 : baseList.all (fun b => decide (∀ e ∈ ({1,2,3,5} : Finset V) \ b,
    ∃ f ∈ b \ ({1,2,3,5} : Finset V), insert f (({1,2,3,5} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_37 : baseList.all (fun b => decide (∀ e ∈ ({1,2,3,6} : Finset V) \ b,
    ∃ f ∈ b \ ({1,2,3,6} : Finset V), insert f (({1,2,3,6} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_38 : baseList.all (fun b => decide (∀ e ∈ ({1,2,3,7} : Finset V) \ b,
    ∃ f ∈ b \ ({1,2,3,7} : Finset V), insert f (({1,2,3,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_39 : baseList.all (fun b => decide (∀ e ∈ ({1,2,3,8} : Finset V) \ b,
    ∃ f ∈ b \ ({1,2,3,8} : Finset V), insert f (({1,2,3,8} : Finset V).erase e) ∈ bases)) = true := by decide
end CommonBasis332371
