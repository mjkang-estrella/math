import Bases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CommonBasis332371
theorem check_60 : baseList.all (fun b => decide (∀ e ∈ ({2,4,5,7} : Finset V) \ b,
    ∃ f ∈ b \ ({2,4,5,7} : Finset V), insert f (({2,4,5,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_61 : baseList.all (fun b => decide (∀ e ∈ ({2,4,6,8} : Finset V) \ b,
    ∃ f ∈ b \ ({2,4,6,8} : Finset V), insert f (({2,4,6,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_62 : baseList.all (fun b => decide (∀ e ∈ ({2,4,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({2,4,7,8} : Finset V), insert f (({2,4,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_63 : baseList.all (fun b => decide (∀ e ∈ ({2,5,6,8} : Finset V) \ b,
    ∃ f ∈ b \ ({2,5,6,8} : Finset V), insert f (({2,5,6,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_64 : baseList.all (fun b => decide (∀ e ∈ ({2,5,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({2,5,7,8} : Finset V), insert f (({2,5,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_65 : baseList.all (fun b => decide (∀ e ∈ ({3,4,5,7} : Finset V) \ b,
    ∃ f ∈ b \ ({3,4,5,7} : Finset V), insert f (({3,4,5,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_66 : baseList.all (fun b => decide (∀ e ∈ ({3,4,5,8} : Finset V) \ b,
    ∃ f ∈ b \ ({3,4,5,8} : Finset V), insert f (({3,4,5,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_67 : baseList.all (fun b => decide (∀ e ∈ ({3,4,6,7} : Finset V) \ b,
    ∃ f ∈ b \ ({3,4,6,7} : Finset V), insert f (({3,4,6,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_68 : baseList.all (fun b => decide (∀ e ∈ ({3,4,6,8} : Finset V) \ b,
    ∃ f ∈ b \ ({3,4,6,8} : Finset V), insert f (({3,4,6,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_69 : baseList.all (fun b => decide (∀ e ∈ ({3,5,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({3,5,7,8} : Finset V), insert f (({3,5,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
end CommonBasis332371
