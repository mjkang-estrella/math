from pathlib import Path
root=Path(__file__).resolve().parent.parent
for m in range(1,21):
 b=min(m,21-m)
 text='import StackSortSeeds2Data\nimport Mathlib.Tactic.FinCases\nnamespace StackSort.Seeds2\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
 for r in range(b+1):
  text+=f'theorem row_valid_{m}_{r} : ∀ s : Fin {b+1},\n (tableX {m} {r} s, tableI {m} {r} s) = topStep tableX tableI {m} {r} s := by decide\n'
 text+=f'theorem row_valid_{m} : ∀ r s : Fin {b+1},\n (tableX {m} r s, tableI {m} r s) = topStep tableX tableI {m} r s := by\n intro r s\n fin_cases r\n'
 for r in range(b+1):text+=f' · exact row_valid_{m}_{r} s\n'
 text+='end StackSort.Seeds2\n'
 (root/f'StackSortSeeds2Row{m:02}.lean').write_text(text)
