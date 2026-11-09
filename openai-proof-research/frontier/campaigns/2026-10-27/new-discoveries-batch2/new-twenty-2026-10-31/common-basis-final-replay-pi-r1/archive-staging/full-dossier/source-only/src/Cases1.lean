import Bases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CommonBasis332371
theorem check_10 : baseList.all (fun b => decide (∀ e ∈ ({0,1,6,7} : Finset V) \ b,
    ∃ f ∈ b \ ({0,1,6,7} : Finset V), insert f (({0,1,6,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_11 : baseList.all (fun b => decide (∀ e ∈ ({0,1,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({0,1,7,8} : Finset V), insert f (({0,1,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_12 : baseList.all (fun b => decide (∀ e ∈ ({0,2,3,5} : Finset V) \ b,
    ∃ f ∈ b \ ({0,2,3,5} : Finset V), insert f (({0,2,3,5} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_13 : baseList.all (fun b => decide (∀ e ∈ ({0,2,3,6} : Finset V) \ b,
    ∃ f ∈ b \ ({0,2,3,6} : Finset V), insert f (({0,2,3,6} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_14 : baseList.all (fun b => decide (∀ e ∈ ({0,2,3,7} : Finset V) \ b,
    ∃ f ∈ b \ ({0,2,3,7} : Finset V), insert f (({0,2,3,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_15 : baseList.all (fun b => decide (∀ e ∈ ({0,2,3,8} : Finset V) \ b,
    ∃ f ∈ b \ ({0,2,3,8} : Finset V), insert f (({0,2,3,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_16 : baseList.all (fun b => decide (∀ e ∈ ({0,2,4,5} : Finset V) \ b,
    ∃ f ∈ b \ ({0,2,4,5} : Finset V), insert f (({0,2,4,5} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_17 : baseList.all (fun b => decide (∀ e ∈ ({0,2,4,6} : Finset V) \ b,
    ∃ f ∈ b \ ({0,2,4,6} : Finset V), insert f (({0,2,4,6} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_18 : baseList.all (fun b => decide (∀ e ∈ ({0,2,4,7} : Finset V) \ b,
    ∃ f ∈ b \ ({0,2,4,7} : Finset V), insert f (({0,2,4,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_19 : baseList.all (fun b => decide (∀ e ∈ ({0,2,4,8} : Finset V) \ b,
    ∃ f ∈ b \ ({0,2,4,8} : Finset V), insert f (({0,2,4,8} : Finset V).erase e) ∈ bases)) = true := by decide
end CommonBasis332371
