import BFSGeneral
namespace EBC337062
open SimpleGraph Finset
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-- A minimum walk containing an oriented edge splits into minimum subwalks. -/
theorem oriented_split_lengths {x y u v : V} (h : G.Adj u v)
    (w : G.Walk x y) (hw : w.length = G.dist x y)
    (p : G.Walk x u) (q : G.Walk v y)
    (he : w = (p.append h.toWalk).append q) :
    p.length = G.dist x u ∧ q.length = G.dist v y ∧
      G.dist x u + 1 + G.dist v y = G.dist x y := by
  have hp : p.IsSubwalk w := ⟨.nil, h.toWalk.append q, by simp [he, ← Walk.append_assoc]⟩
  have hq : q.IsSubwalk w := ⟨p.append h.toWalk, .nil, by simp [he]⟩
  have ep := SimpleGraph.length_eq_dist_of_subwalk hw hp
  have eq := SimpleGraph.length_eq_dist_of_subwalk hw hq
  refine ⟨ep, eq, ?_⟩
  simpa [he, Walk.length_append, ep, eq] using hw

/-- Concatenation at a fixed prefix length is injective on pairs of walks. -/
theorem concat_pair_injective {x y u v : V} (h : G.Adj u v)
    (p p' : G.Walk x u) (q q' : G.Walk v y)
    (hl : p.length = p'.length)
    (he : p.append (Walk.cons h q) = p'.append (Walk.cons h q')) : p = p' ∧ q = q' := by
  have hd := congrArg Walk.darts he
  simp only [Walk.darts_append] at hd
  have hh := List.append_inj hd (by simpa using hl)
  refine ⟨Walk.darts_injective hh.1, ?_⟩
  have hc : (Walk.cons h q) = (Walk.cons h q') := Walk.darts_injective hh.2
  simpa using hc

noncomputable def orientedPaths (x y u v : V) (h : G.Adj u v) : Finset (G.Walk x y) := by
  classical
  exact (G.finsetWalkLength (G.dist x y) x y).filter (fun w => h.toWalk.IsSubwalk w)

theorem orientedPaths_card (x y u v : V) (h : G.Adj u v) :
    (orientedPaths G x y u v h).card =
      if G.dist x u + 1 + G.dist v y = G.dist x y
      then sigma G x u * sigma G v y else 0 := by
  classical
  by_cases heq : G.dist x u + 1 + G.dist v y = G.dist x y
  · rw [ite_eq_left heq, sigma_eq_walk_count, sigma_eq_walk_count, ← Finset.card_product]
    symm
    apply Finset.card_bij (fun pq _ => pq.1.append (Walk.cons h pq.2))
    · intro pq hpq
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
      apply Finset.mem_filter.mpr
      constructor
      · apply G.mem_finsetWalkLength_iff.mpr
        simpa [Walk.length_append, G.mem_finsetWalkLength_iff.mp hp,
          G.mem_finsetWalkLength_iff.mp hq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq
      · exact ⟨pq.1, pq.2, by simp [← Walk.append_assoc]⟩
    · intro pq hpq rs hrs he
      have hp := G.mem_finsetWalkLength_iff.mp (Finset.mem_product.mp hpq).1
      have hr := G.mem_finsetWalkLength_iff.mp (Finset.mem_product.mp hrs).1
      exact Prod.ext (concat_pair_injective G h _ _ _ _ (hp.trans hr.symm) he).1
        (concat_pair_injective G h _ _ _ _ (hp.trans hr.symm) he).2
    · intro w hw
      obtain ⟨hm, p, q, he⟩ := Finset.mem_filter.mp hw
      have hh := oriented_split_lengths G h w (G.mem_finsetWalkLength_iff.mp hm) p q he
      refine ⟨(p,q), Finset.mem_product.mpr ⟨G.mem_finsetWalkLength_iff.mpr hh.1,
        G.mem_finsetWalkLength_iff.mpr hh.2.1⟩, ?_⟩
      simpa [← Walk.append_assoc] using he.symm
  · rw [ite_eq_right heq]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hm, p, q, he⟩ := Finset.mem_filter.mp hw
    exact heq (oriented_split_lengths G h w (G.mem_finsetWalkLength_iff.mp hm) p q he).2.2

/-- A geodesic cannot traverse an edge in both orientations. -/
theorem orientedPaths_disjoint (conn : G.Connected) (x y u v : V) (h : G.Adj u v) :
    Disjoint (orientedPaths G x y u v h) (orientedPaths G x y v u h.symm) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  obtain ⟨hm, p, q, he⟩ := Finset.mem_filter.mp hw
  obtain ⟨_, p', q', he'⟩ := Finset.mem_filter.mp hw'
  have hlen := G.mem_finsetWalkLength_iff.mp hm
  have h1 := (oriented_split_lengths G h w hlen p q he).2.2
  have h2 := (oriented_split_lengths G h.symm w hlen p' q' he').2.2
  have h3 := conn.dist_triangle (u := x) (v := u) (w := y)
  have h4 := conn.dist_triangle (u := x) (v := v) (w := y)
  omega

/-- General shortest-path edge splitting, for every connected finite graph. -/
theorem sigmaEdge_split (conn : G.Connected) (x y u v : V) (h : G.Adj u v) :
    sigmaEdge G x y s(u,v) =
      (if G.dist x u + 1 + G.dist v y = G.dist x y then
        sigma G x u * sigma G v y else 0) +
      (if G.dist x v + 1 + G.dist u y = G.dist x y then
        sigma G x v * sigma G u y else 0) := by
  classical
  rw [← orientedPaths_card G x y u v h, ← orientedPaths_card G x y v u h.symm,
    ← Finset.card_union_of_disjoint (orientedPaths_disjoint G conn x y u v h)]
  unfold sigmaEdge
  rw [shortestPaths_eq]
  congr 1
  ext w
  simp only [orientedPaths, Finset.mem_filter, Finset.mem_union]
  rw [← Walk.isSubwalk_toWalk_iff_mem_edges h]
  tauto
end EBC337062
