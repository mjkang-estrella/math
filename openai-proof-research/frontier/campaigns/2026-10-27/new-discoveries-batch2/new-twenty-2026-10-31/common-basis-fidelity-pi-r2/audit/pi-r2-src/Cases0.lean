import Bases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CommonBasis332371
theorem check_0 : baseList.all (fun b => decide (∀ e ∈ ({0,1,2,5} : Finset V) \ b,
    ∃ f ∈ b \ ({0,1,2,5} : Finset V), insert f (({0,1,2,5} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_1 : baseList.all (fun b => decide (∀ e ∈ ({0,1,2,6} : Finset V) \ b,
    ∃ f ∈ b \ ({0,1,2,6} : Finset V), insert f (({0,1,2,6} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_2 : baseList.all (fun b => decide (∀ e ∈ ({0,1,2,7} : Finset V) \ b,
    ∃ f ∈ b \ ({0,1,2,7} : Finset V), insert f (({0,1,2,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_3 : baseList.all (fun b => decide (∀ e ∈ ({0,1,2,8} : Finset V) \ b,
    ∃ f ∈ b \ ({0,1,2,8} : Finset V), insert f (({0,1,2,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_4 : baseList.all (fun b => decide (∀ e ∈ ({0,1,3,5} : Finset V) \ b,
    ∃ f ∈ b \ ({0,1,3,5} : Finset V), insert f (({0,1,3,5} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_5 : baseList.all (fun b => decide (∀ e ∈ ({0,1,3,6} : Finset V) \ b,
    ∃ f ∈ b \ ({0,1,3,6} : Finset V), insert f (({0,1,3,6} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_6 : baseList.all (fun b => decide (∀ e ∈ ({0,1,3,7} : Finset V) \ b,
    ∃ f ∈ b \ ({0,1,3,7} : Finset V), insert f (({0,1,3,7} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_7 : baseList.all (fun b => decide (∀ e ∈ ({0,1,3,8} : Finset V) \ b,
    ∃ f ∈ b \ ({0,1,3,8} : Finset V), insert f (({0,1,3,8} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_8 : baseList.all (fun b => decide (∀ e ∈ ({0,1,5,6} : Finset V) \ b,
    ∃ f ∈ b \ ({0,1,5,6} : Finset V), insert f (({0,1,5,6} : Finset V).erase e) ∈ bases)) = true := by decide
theorem check_9 : baseList.all (fun b => decide (∀ e ∈ ({0,1,5,8} : Finset V) \ b,
    ∃ f ∈ b \ ({0,1,5,8} : Finset V), insert f (({0,1,5,8} : Finset V).erase e) ∈ bases)) = true := by decide
end CommonBasis332371
