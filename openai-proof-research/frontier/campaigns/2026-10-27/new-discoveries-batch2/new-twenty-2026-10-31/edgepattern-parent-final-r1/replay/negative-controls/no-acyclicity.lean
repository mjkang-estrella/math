import EndpointR5
open EdgePattern.TreeModelsR5
example {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
  (f : G →g H) (hi : Function.Injective f) (hc : G.Connected) {x y : V}
  (h : H.Adj (f x) (f y)) : G.Adj x y := by
  exact reflects_adjacency f hi hc h
