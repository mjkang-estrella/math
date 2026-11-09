import Magic
set_option warningAsError true
open Magic381805
def bad : V → ℕ := ![3,3,4,5,8,6,1,7,9,10,11]
example : Function.Injective bad := by decide
