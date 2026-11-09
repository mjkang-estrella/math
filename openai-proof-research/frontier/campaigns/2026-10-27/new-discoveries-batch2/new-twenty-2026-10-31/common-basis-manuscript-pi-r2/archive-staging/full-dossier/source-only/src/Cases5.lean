import Bases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CommonBasis332371
theorem check_50 : baseList.all (fun b => decide (∀ e ∈ ({1,5,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({1,5,7,8} : Finset V), insert f (({1,5,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_51 : baseList.all (fun b => decide (∀ e ∈ ({1,6,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({1,6,7,8} : Finset V), insert f (({1,6,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_52 : baseList.all (fun b => decide (∀ e ∈ ({2,3,4,5} : Finset V) \ b,
    ∃ f ∈ b \ ({2,3,4,5} : Finset V), insert f (({2,3,4,5} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_53 : baseList.all (fun b => decide (∀ e ∈ ({2,3,4,6} : Finset V) \ b,
    ∃ f ∈ b \ ({2,3,4,6} : Finset V), insert f (({2,3,4,6} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_54 : baseList.all (fun b => decide (∀ e ∈ ({2,3,4,7} : Finset V) \ b,
    ∃ f ∈ b \ ({2,3,4,7} : Finset V), insert f (({2,3,4,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_55 : baseList.all (fun b => decide (∀ e ∈ ({2,3,4,8} : Finset V) \ b,
    ∃ f ∈ b \ ({2,3,4,8} : Finset V), insert f (({2,3,4,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_56 : baseList.all (fun b => decide (∀ e ∈ ({2,3,5,8} : Finset V) \ b,
    ∃ f ∈ b \ ({2,3,5,8} : Finset V), insert f (({2,3,5,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_57 : baseList.all (fun b => decide (∀ e ∈ ({2,3,6,8} : Finset V) \ b,
    ∃ f ∈ b \ ({2,3,6,8} : Finset V), insert f (({2,3,6,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_58 : baseList.all (fun b => decide (∀ e ∈ ({2,3,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({2,3,7,8} : Finset V), insert f (({2,3,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_59 : baseList.all (fun b => decide (∀ e ∈ ({2,4,5,6} : Finset V) \ b,
    ∃ f ∈ b \ ({2,4,5,6} : Finset V), insert f (({2,4,5,6} : Finset V).erase e) ∈ bases)) = true := by decide
end CommonBasis332371
