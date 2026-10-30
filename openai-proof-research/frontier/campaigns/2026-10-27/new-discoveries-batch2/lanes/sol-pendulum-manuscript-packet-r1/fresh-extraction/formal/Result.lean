module
public import Series
public import EndpointTransfer
public section
noncomputable section
namespace PendulumTimeMap
theorem source_claim : SourceClaim :=
  sourceClaim_of_interior_convex (fun _ hp hp2 => sourceTime_interior_convex hp hp2)
end PendulumTimeMap
