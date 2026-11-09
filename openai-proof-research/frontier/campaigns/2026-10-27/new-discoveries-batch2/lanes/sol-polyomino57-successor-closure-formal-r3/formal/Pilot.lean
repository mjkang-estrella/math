import Witness
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Polyomino57
def pilotPiece0 : List GridPoint := [(-9,1),(-8,1),(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement0 : translate (4,-1) pilotPiece0.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece0 (4,-1) (by decide)
def pilotPiece1 : List GridPoint := [(-8,1),(-8,2),(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement1 : translate (4,-1) pilotPiece1.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece1 (4,-1) (by decide)
def pilotPiece2 : List GridPoint := [(-8,1),(-7,1),(-7,2),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement2 : translate (3,-1) pilotPiece2.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece2 (3,-1) (by decide)
def pilotPiece3 : List GridPoint := [(-8,1),(-7,1),(-6,1),(-6,2),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement3 : translate (3,-1) pilotPiece3.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece3 (3,-1) (by decide)
def pilotPiece4 : List GridPoint := [(-8,1),(-7,1),(-6,1),(-5,1),(-5,2),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement4 : translate (3,-1) pilotPiece4.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece4 (3,-1) (by decide)
def pilotPiece5 : List GridPoint := [(-8,1),(-7,1),(-6,1),(-5,1),(-4,1),(-4,2),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement5 : translate (3,-1) pilotPiece5.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece5 (3,-1) (by decide)
def pilotPiece6 : List GridPoint := [(-8,1),(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-3,2),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement6 : translate (3,-1) pilotPiece6.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece6 (3,-1) (by decide)
def pilotPiece7 : List GridPoint := [(-8,1),(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-2,2),(-1,1),(0,0),(0,1)]
theorem pilotPlacement7 : translate (3,-1) pilotPiece7.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece7 (3,-1) (by decide)
def pilotPiece8 : List GridPoint := [(-8,1),(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(-1,2),(0,0),(0,1)]
theorem pilotPlacement8 : translate (3,-1) pilotPiece8.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece8 (3,-1) (by decide)
def pilotPiece9 : List GridPoint := [(-8,1),(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(0,2)]
theorem pilotPlacement9 : translate (3,-1) pilotPiece9.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece9 (3,-1) (by decide)
def pilotPiece10 : List GridPoint := [(-8,1),(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(1,0)]
theorem pilotPlacement10 : translate (3,-1) pilotPiece10.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece10 (3,-1) (by decide)
def pilotPiece11 : List GridPoint := [(-8,1),(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(1,1)]
theorem pilotPlacement11 : translate (3,-1) pilotPiece11.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece11 (3,-1) (by decide)
def pilotPiece12 : List GridPoint := [(-8,2),(-7,1),(-7,2),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement12 : translate (3,-2) pilotPiece12.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece12 (3,-2) (by decide)
def pilotPiece13 : List GridPoint := [(-7,1),(-7,2),(-7,3),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement13 : translate (3,-2) pilotPiece13.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece13 (3,-2) (by decide)
def pilotPiece14 : List GridPoint := [(-7,1),(-7,2),(-6,1),(-6,2),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement14 : translate (3,-2) pilotPiece14.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece14 (3,-2) (by decide)
def pilotPiece15 : List GridPoint := [(-7,1),(-7,2),(-6,1),(-5,1),(-5,2),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement15 : translate (3,-2) pilotPiece15.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece15 (3,-2) (by decide)
def pilotPiece16 : List GridPoint := [(-7,1),(-7,2),(-6,1),(-5,1),(-4,1),(-4,2),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement16 : translate (3,-2) pilotPiece16.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece16 (3,-2) (by decide)
def pilotPiece17 : List GridPoint := [(-7,1),(-7,2),(-6,1),(-5,1),(-4,1),(-3,1),(-3,2),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement17 : translate (3,-2) pilotPiece17.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece17 (3,-2) (by decide)
def pilotPiece18 : List GridPoint := [(-7,1),(-7,2),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-2,2),(-1,1),(0,0),(0,1)]
theorem pilotPlacement18 : translate (3,-2) pilotPiece18.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece18 (3,-2) (by decide)
def pilotPiece19 : List GridPoint := [(-7,1),(-7,2),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(-1,2),(0,0),(0,1)]
theorem pilotPlacement19 : translate (3,-2) pilotPiece19.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece19 (3,-2) (by decide)
def pilotPiece20 : List GridPoint := [(-7,1),(-7,2),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(0,2)]
theorem pilotPlacement20 : translate (3,-2) pilotPiece20.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece20 (3,-2) (by decide)
def pilotPiece21 : List GridPoint := [(-7,1),(-7,2),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(1,0)]
theorem pilotPlacement21 : translate (3,-1) pilotPiece21.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece21 (3,-1) (by decide)
def pilotPiece22 : List GridPoint := [(-7,1),(-7,2),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(1,1)]
theorem pilotPlacement22 : translate (3,-2) pilotPiece22.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece22 (3,-2) (by decide)
def pilotPiece23 : List GridPoint := [(-7,1),(-6,1),(-6,2),(-6,3),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement23 : translate (3,-2) pilotPiece23.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece23 (3,-2) (by decide)
def pilotPiece24 : List GridPoint := [(-7,1),(-6,1),(-6,2),(-5,1),(-5,2),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement24 : translate (2,-1) pilotPiece24.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece24 (2,-1) (by decide)
def pilotPiece25 : List GridPoint := [(-7,1),(-6,1),(-6,2),(-5,1),(-4,1),(-4,2),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement25 : translate (2,-1) pilotPiece25.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece25 (2,-1) (by decide)
def pilotPiece26 : List GridPoint := [(-7,1),(-6,1),(-6,2),(-5,1),(-4,1),(-3,1),(-3,2),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement26 : translate (2,-1) pilotPiece26.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece26 (2,-1) (by decide)
def pilotPiece27 : List GridPoint := [(-7,1),(-6,1),(-6,2),(-5,1),(-4,1),(-3,1),(-2,1),(-2,2),(-1,1),(0,0),(0,1)]
theorem pilotPlacement27 : translate (2,-1) pilotPiece27.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece27 (2,-1) (by decide)
def pilotPiece28 : List GridPoint := [(-7,1),(-6,1),(-6,2),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(-1,2),(0,0),(0,1)]
theorem pilotPlacement28 : translate (2,-1) pilotPiece28.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece28 (2,-1) (by decide)
def pilotPiece29 : List GridPoint := [(-7,1),(-6,1),(-6,2),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(0,2)]
theorem pilotPlacement29 : translate (2,-1) pilotPiece29.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece29 (2,-1) (by decide)
def pilotPiece30 : List GridPoint := [(-7,1),(-6,1),(-6,2),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(1,0)]
theorem pilotPlacement30 : translate (2,-1) pilotPiece30.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece30 (2,-1) (by decide)
def pilotPiece31 : List GridPoint := [(-7,1),(-6,1),(-6,2),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(1,1)]
theorem pilotPlacement31 : translate (2,-1) pilotPiece31.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece31 (2,-1) (by decide)
def pilotPiece32 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-5,2),(-5,3),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement32 : translate (2,-1) pilotPiece32.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece32 (2,-1) (by decide)
def pilotPiece33 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-5,2),(-4,1),(-4,2),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement33 : translate (2,-1) pilotPiece33.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece33 (2,-1) (by decide)
def pilotPiece34 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-5,2),(-4,1),(-3,1),(-3,2),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement34 : translate (2,-1) pilotPiece34.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece34 (2,-1) (by decide)
def pilotPiece35 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-5,2),(-4,1),(-3,1),(-2,1),(-2,2),(-1,1),(0,0),(0,1)]
theorem pilotPlacement35 : translate (2,-1) pilotPiece35.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece35 (2,-1) (by decide)
def pilotPiece36 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-5,2),(-4,1),(-3,1),(-2,1),(-1,1),(-1,2),(0,0),(0,1)]
theorem pilotPlacement36 : translate (2,-1) pilotPiece36.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece36 (2,-1) (by decide)
def pilotPiece37 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-5,2),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(0,2)]
theorem pilotPlacement37 : translate (2,-1) pilotPiece37.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece37 (2,-1) (by decide)
def pilotPiece38 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-5,2),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(1,0)]
theorem pilotPlacement38 : translate (2,-1) pilotPiece38.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece38 (2,-1) (by decide)
def pilotPiece39 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-5,2),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(1,1)]
theorem pilotPlacement39 : translate (2,-1) pilotPiece39.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece39 (2,-1) (by decide)
def pilotPiece40 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-4,2),(-4,3),(-3,1),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement40 : translate (3,-2) pilotPiece40.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece40 (3,-2) (by decide)
def pilotPiece41 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-4,2),(-3,1),(-3,2),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement41 : translate (2,-1) pilotPiece41.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece41 (2,-1) (by decide)
def pilotPiece42 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-4,2),(-3,1),(-2,1),(-2,2),(-1,1),(0,0),(0,1)]
theorem pilotPlacement42 : translate (2,-1) pilotPiece42.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece42 (2,-1) (by decide)
def pilotPiece43 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-4,2),(-3,1),(-2,1),(-1,1),(-1,2),(0,0),(0,1)]
theorem pilotPlacement43 : translate (2,-1) pilotPiece43.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece43 (2,-1) (by decide)
def pilotPiece44 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-4,2),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(0,2)]
theorem pilotPlacement44 : translate (2,-1) pilotPiece44.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece44 (2,-1) (by decide)
def pilotPiece45 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-4,2),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(1,0)]
theorem pilotPlacement45 : translate (2,-1) pilotPiece45.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece45 (2,-1) (by decide)
def pilotPiece46 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-4,2),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(1,1)]
theorem pilotPlacement46 : translate (2,-1) pilotPiece46.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece46 (2,-1) (by decide)
def pilotPiece47 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-3,2),(-3,3),(-2,1),(-1,1),(0,0),(0,1)]
theorem pilotPlacement47 : translate (2,-1) pilotPiece47.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece47 (2,-1) (by decide)
def pilotPiece48 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-3,2),(-2,1),(-2,2),(-1,1),(0,0),(0,1)]
theorem pilotPlacement48 : translate (2,-1) pilotPiece48.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece48 (2,-1) (by decide)
def pilotPiece49 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-3,2),(-2,1),(-1,1),(-1,2),(0,0),(0,1)]
theorem pilotPlacement49 : translate (2,-1) pilotPiece49.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece49 (2,-1) (by decide)
def pilotPiece50 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-3,2),(-2,1),(-1,1),(0,0),(0,1),(0,2)]
theorem pilotPlacement50 : translate (2,-1) pilotPiece50.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece50 (2,-1) (by decide)
def pilotPiece51 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-3,2),(-2,1),(-1,1),(0,0),(0,1),(1,0)]
theorem pilotPlacement51 : translate (2,-1) pilotPiece51.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece51 (2,-1) (by decide)
def pilotPiece52 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-3,2),(-2,1),(-1,1),(0,0),(0,1),(1,1)]
theorem pilotPlacement52 : translate (2,-1) pilotPiece52.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece52 (2,-1) (by decide)
def pilotPiece53 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-2,2),(-2,3),(-1,1),(0,0),(0,1)]
theorem pilotPlacement53 : translate (2,-1) pilotPiece53.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece53 (2,-1) (by decide)
def pilotPiece54 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-2,2),(-1,1),(-1,2),(0,0),(0,1)]
theorem pilotPlacement54 : translate (2,-1) pilotPiece54.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece54 (2,-1) (by decide)
def pilotPiece55 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-2,2),(-1,1),(0,0),(0,1),(0,2)]
theorem pilotPlacement55 : translate (2,-1) pilotPiece55.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece55 (2,-1) (by decide)
def pilotPiece56 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-2,2),(-1,1),(0,0),(0,1),(1,0)]
theorem pilotPlacement56 : translate (2,-1) pilotPiece56.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece56 (2,-1) (by decide)
def pilotPiece57 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-2,2),(-1,1),(0,0),(0,1),(1,1)]
theorem pilotPlacement57 : translate (2,-1) pilotPiece57.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece57 (2,-1) (by decide)
def pilotPiece58 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(-1,2),(-1,3),(0,0),(0,1)]
theorem pilotPlacement58 : translate (2,-1) pilotPiece58.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece58 (2,-1) (by decide)
def pilotPiece59 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(-1,2),(0,0),(0,1),(0,2)]
theorem pilotPlacement59 : translate (2,-1) pilotPiece59.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece59 (2,-1) (by decide)
def pilotPiece60 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(-1,2),(0,0),(0,1),(1,0)]
theorem pilotPlacement60 : translate (2,-1) pilotPiece60.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece60 (2,-1) (by decide)
def pilotPiece61 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(-1,2),(0,0),(0,1),(1,1)]
theorem pilotPlacement61 : translate (2,-1) pilotPiece61.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece61 (2,-1) (by decide)
def pilotPiece62 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(0,2),(0,3)]
theorem pilotPlacement62 : translate (3,-2) pilotPiece62.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece62 (3,-2) (by decide)
def pilotPiece63 : List GridPoint := [(-7,1),(-6,1),(-5,1),(-4,1),(-3,1),(-2,1),(-1,1),(0,0),(0,1),(0,2),(1,0)]
theorem pilotPlacement63 : translate (2,-1) pilotPiece63.toFinset ⊆ witness :=
  placementCheck_sound witness pilotPiece63 (2,-1) (by decide)
end Polyomino57
