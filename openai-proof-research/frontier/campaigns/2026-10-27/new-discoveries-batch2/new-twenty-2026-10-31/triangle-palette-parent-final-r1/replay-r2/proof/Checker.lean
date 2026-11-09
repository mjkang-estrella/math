import BoolProbe
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option warningAsError true
namespace Palette
def check10 (a : C) (b : C) (c : C) (d : C) (e : C) (f : C) (g : C) (h : C) (i : C) (j : C) : Bool :=
  if (code a b e) = (code c d j) then true else if (code a b e) = (code f g j) then true else if (code a b e) = (code h i j) then true else if (code a c f) = (code c d j) then true else if (code a c f) = (code f g j) then true else if (code a c f) = (code h i j) then true else if (code a d g) = (code c d j) then true else if (code a d g) = (code f g j) then true else if (code a d g) = (code h i j) then true else if (code b c h) = (code c d j) then true else if (code b c h) = (code f g j) then true else if (code b c h) = (code h i j) then true else if (code b d i) = (code c d j) then true else if (code b d i) = (code f g j) then true else if (code b d i) = (code h i j) then true else if (code c d j) = (code e f h) then true else if (code c d j) = (code e g i) then true else if (code c d j) = (code f g j) then true else if (code c d j) = (code h i j) then true else if (code e f h) = (code f g j) then true else if (code e f h) = (code h i j) then true else if (code e g i) = (code f g j) then true else if (code e g i) = (code h i j) then true else if (code f g j) = (code h i j) then true else false

def check9 (a : C) (b : C) (c : C) (d : C) (e : C) (f : C) (g : C) (h : C) (i : C) : Bool :=
  if (code a b e) = (code b d i) then true else if (code a b e) = (code e g i) then true else if (code a c f) = (code b d i) then true else if (code a c f) = (code e g i) then true else if (code a d g) = (code b d i) then true else if (code a d g) = (code e g i) then true else if (code b c h) = (code b d i) then true else if (code b c h) = (code e g i) then true else if (code b d i) = (code e f h) then true else if (code b d i) = (code e g i) then true else if (code e f h) = (code e g i) then true else all4 fun j => check10 a b c d e f g h i j

def check8 (a : C) (b : C) (c : C) (d : C) (e : C) (f : C) (g : C) (h : C) : Bool :=
  if (code a b e) = (code b c h) then true else if (code a b e) = (code e f h) then true else if (code a c f) = (code b c h) then true else if (code a c f) = (code e f h) then true else if (code a d g) = (code b c h) then true else if (code a d g) = (code e f h) then true else if (code b c h) = (code e f h) then true else all4 fun i => check9 a b c d e f g h i

def check7 (a : C) (b : C) (c : C) (d : C) (e : C) (f : C) (g : C) : Bool :=
  if (code a b e) = (code a d g) then true else if (code a c f) = (code a d g) then true else all4 fun h => check8 a b c d e f g h

def check6 (a : C) (b : C) (c : C) (d : C) (e : C) (f : C) : Bool :=
  if (code a b e) = (code a c f) then true else all4 fun g => check7 a b c d e f g

def check5 (a : C) (b : C) (c : C) (d : C) (e : C) : Bool :=
  all4 fun f => check6 a b c d e f

def check4 (a : C) (b : C) (c : C) (d : C) : Bool :=
  all4 fun e => check5 a b c d e

def check3 (a : C) (b : C) (c : C) : Bool :=
  all4 fun d => check4 a b c d

def check2 (a : C) (b : C) : Bool :=
  all4 fun c => check3 a b c

def check1 (a : C) : Bool :=
  all4 fun b => check2 a b

def check0  : Bool :=
  all4 fun a => check1 a

theorem check_pass : check0 = true := by decide
end Palette
