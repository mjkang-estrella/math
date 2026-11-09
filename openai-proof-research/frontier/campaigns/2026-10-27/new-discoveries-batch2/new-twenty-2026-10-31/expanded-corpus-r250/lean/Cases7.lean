import Bases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CommonBasis332371
theorem check_70 : baseList.all (fun b => decide (∀ e ∈ ({3,6,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({3,6,7,8} : Finset V), insert f (({3,6,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_71 : baseList.all (fun b => decide (∀ e ∈ ({4,5,6,7} : Finset V) \ b,
    ∃ f ∈ b \ ({4,5,6,7} : Finset V), insert f (({4,5,6,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_72 : baseList.all (fun b => decide (∀ e ∈ ({4,5,6,8} : Finset V) \ b,
    ∃ f ∈ b \ ({4,5,6,8} : Finset V), insert f (({4,5,6,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_73 : baseList.all (fun b => decide (∀ e ∈ ({4,5,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({4,5,7,8} : Finset V), insert f (({4,5,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_74 : baseList.all (fun b => decide (∀ e ∈ ({4,6,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({4,6,7,8} : Finset V), insert f (({4,6,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_75 : baseList.all (fun b => decide (∀ e ∈ ({5,6,7,8} : Finset V) \ b,
    ∃ f ∈ b \ ({5,6,7,8} : Finset V), insert f (({5,6,7,8} : Finset V).erase e) ∈ bases)) = true := by decide
end CommonBasis332371
