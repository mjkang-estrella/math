import Bases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CommonBasis332371
theorem check_40 : baseList.all (fun b => decide (∀ e ∈ ({1,2,5,6} : Finset V) \ b,
    ∃ f ∈ b \ ({1,2,5,6} : Finset V), insert f (({1,2,5,6} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_41 : baseList.all (fun b => decide (∀ e ∈ ({1,2,5,7} : Finset V) \ b,
    ∃ f ∈ b \ ({1,2,5,7} : Finset V), insert f (({1,2,5,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_42 : baseList.all (fun b => decide (∀ e ∈ ({1,2,6,8} : Finset V) \ b,
    ∃ f ∈ b \ ({1,2,6,8} : Finset V), insert f (({1,2,6,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_43 : baseList.all (fun b => decide (∀ e ∈ ({1,2,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({1,2,7,8} : Finset V), insert f (({1,2,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_44 : baseList.all (fun b => decide (∀ e ∈ ({1,3,5,7} : Finset V) \ b,
    ∃ f ∈ b \ ({1,3,5,7} : Finset V), insert f (({1,3,5,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_45 : baseList.all (fun b => decide (∀ e ∈ ({1,3,5,8} : Finset V) \ b,
    ∃ f ∈ b \ ({1,3,5,8} : Finset V), insert f (({1,3,5,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_46 : baseList.all (fun b => decide (∀ e ∈ ({1,3,6,7} : Finset V) \ b,
    ∃ f ∈ b \ ({1,3,6,7} : Finset V), insert f (({1,3,6,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_47 : baseList.all (fun b => decide (∀ e ∈ ({1,3,6,8} : Finset V) \ b,
    ∃ f ∈ b \ ({1,3,6,8} : Finset V), insert f (({1,3,6,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_48 : baseList.all (fun b => decide (∀ e ∈ ({1,5,6,7} : Finset V) \ b,
    ∃ f ∈ b \ ({1,5,6,7} : Finset V), insert f (({1,5,6,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_49 : baseList.all (fun b => decide (∀ e ∈ ({1,5,6,8} : Finset V) \ b,
    ∃ f ∈ b \ ({1,5,6,8} : Finset V), insert f (({1,5,6,8} : Finset V).erase e) ∈ bases)) = true := by decide
end CommonBasis332371
