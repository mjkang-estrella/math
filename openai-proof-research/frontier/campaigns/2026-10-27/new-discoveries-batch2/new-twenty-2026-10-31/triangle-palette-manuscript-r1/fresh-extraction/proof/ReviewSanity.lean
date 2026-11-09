import Endpoint
set_option warningAsError true
set_option pp.all true
set_option pp.proofs true
set_option pp.maxSteps 10000000
#print Palette.C
#print Palette.Edge
#print Palette.Triangle
#print Palette.pal
#print Palette.all4
#print Palette.code
#print Palette.trianglePalette
#print Palette.Achievable
#print Palette.SourceClaim
example : Palette.pal 0 0 1 = Palette.pal 0 1 1 := by decide
example : Fintype.card (Palette.Edge 5) = 10 := by decide
example : Fintype.card (Palette.Triangle 5) = 10 := by decide
example : Palette.trianglePalette (fun _ : Palette.Edge 5 => (0 : Fin 4)) Palette.t0 = {0} := by decide
example : ¬ Function.Injective (Palette.trianglePalette (fun _ : Palette.Edge 5 => (0 : Fin 4))) := Palette.no_four _
