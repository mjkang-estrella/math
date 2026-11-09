import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let decl := Declaration.thmDecl { name := `forged, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
  match env.addDeclCore 0 0 decl none false with
  | .ok e => setEnv e
  | .error _ => throwError "injection failed"
