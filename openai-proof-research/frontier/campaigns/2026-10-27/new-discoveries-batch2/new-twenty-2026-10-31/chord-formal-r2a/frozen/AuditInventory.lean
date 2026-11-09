import ChordFinal
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let lines := env.header.moduleNames.toList.map (fun n => "import " ++ n.toString)
  liftIO <| IO.FS.writeFile "audit-imports.txt" (String.intercalate "\n" lines ++ "\n")
