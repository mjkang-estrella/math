import Mathlib.Data.Finset.Basic
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option warningAsError true
namespace Palette
abbrev C := Fin 4
def pal (a b c : C) : Finset C := {a,b,c}
def Good (a b c d e f g h i j : C) : Prop :=
 ([pal a b e, pal a c f, pal a d g, pal b c h, pal b d i,
   pal c d j, pal e f h, pal e g i, pal f g j, pal h i j]).Nodup
instance (a b c d e f g h i j : C) : Decidable (Good a b c d e f g h i j) := inferInstanceAs (Decidable (List.Nodup _))
end Palette
