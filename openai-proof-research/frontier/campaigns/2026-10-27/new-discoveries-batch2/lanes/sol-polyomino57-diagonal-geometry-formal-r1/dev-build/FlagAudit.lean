import SignedNormalization
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for n in #[`Polyomino57.attachCheck._unsafe_rec] do
  let ci := env.find? n |>.get!
  logInfo m!"{n} unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom} type={ci.type}"
