import PolynexusPartition

/-! Actual zero-pair gap coordinates. The two lengths are `e+1,f+1`.
The three gaps include the possibly empty gap between adjacent intervals.
The last two coordinates are the independent outer starts. -/
abbrev PGapData := (ℕ × ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)

def PGapBox (n : ℕ) : Finset PGapData :=
  ((Finset.range (n+1) ×ˢ Finset.range (n+1) ×ˢ Finset.range (n+1)) ×ˢ
    (Finset.range (n+1) ×ˢ Finset.range (n+1)) ×ˢ
    (Finset.range (n+1) ×ˢ Finset.range (n+1)))

def PGap (n : ℕ) : Finset PGapData := (PGapBox n).filter fun g =>
  g.1.1 + g.1.2.1 + g.1.2.2 + g.2.1.1 + g.2.1.2 + 2 = n ∧
  g.2.2.1 + g.2.1.1 < n ∧ g.2.2.2 + g.2.1.2 < n

def PToGap (n : ℕ) (p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) : PGapData :=
  ((p.1.2.1, p.2.1 - (p.1.2.1 + p.1.2.2 + 1), n - (p.2.1 + p.2.2.2 + 1)),
    (p.1.2.2, p.2.2.2), (p.1.1, p.2.2.1))

def PFromGap (g : PGapData) : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) :=
  ((g.2.2.1, g.1.1, g.2.1.1),
    (g.1.1 + g.2.1.1 + 1 + g.1.2.1, g.2.2.2, g.2.1.2))

theorem PGap_mem {n : ℕ} {g : PGapData} : g ∈ PGap n ↔
    g.1.1 + g.1.2.1 + g.1.2.2 + g.2.1.1 + g.2.1.2 + 2 = n ∧
    g.2.2.1 + g.2.1.1 < n ∧ g.2.2.2 + g.2.1.2 < n := by
  constructor
  · exact fun h => (Finset.mem_filter.1 h).2
  · intro h
    apply Finset.mem_filter.2
    refine ⟨?_, h⟩
    simp only [PGapBox, Finset.mem_product, Finset.mem_range]
    omega

theorem PToGap_mem {n : ℕ} {p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)}
    (hp : p ∈ PLeftT n) : PToGap n p ∈ PGap n := by
  obtain ⟨hx, hy, hl⟩ := mem_leftT hp
  obtain ⟨_, hx1, hx2⟩ := PLeg_mem.1 hx
  obtain ⟨_, hy1, hy2⟩ := PLeg_mem.1 hy
  apply PGap_mem.2
  dsimp [PToGap]
  omega

theorem PFromGap_mem {n : ℕ} {g : PGapData} (hg : g ∈ PGap n) :
    PFromGap g ∈ PLeftT n := by
  have h := PGap_mem.1 hg
  apply mem_leftT'
  · apply PLeg_mem.2
    dsimp [PFromGap]
    omega
  · apply PLeg_mem.2
    dsimp [PFromGap]
    omega
  · dsimp [PFromGap]
    omega

theorem PFromToGap {n : ℕ} {p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)}
    (hp : p ∈ PLeftT n) : PFromGap (PToGap n p) = p := by
  have hl := (mem_leftT hp).2.2
  obtain ⟨⟨a,b,e⟩,⟨c,d,f⟩⟩ := p
  dsimp at hl
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · dsimp [PToGap, PFromGap]
      omega
    · rfl

theorem PToFromGap {n : ℕ} {g : PGapData} (hg : g ∈ PGap n) :
    PToGap n (PFromGap g) = g := by
  have h := PGap_mem.1 hg
  obtain ⟨⟨x,y,z⟩,⟨e,f⟩,⟨a,b⟩⟩ := g
  dsimp at h
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · dsimp [PToGap, PFromGap]
        omega
      · dsimp [PToGap, PFromGap]
        omega
  · rfl

/-- Every actual left zero pair has unique gap data; no matrix outputs
are identified or counted in place of the ordered operands. -/
theorem PLeftT_card_gap (n : ℕ) : (PLeftT n).card = (PGap n).card := by
  apply Finset.card_bij (fun p _ => PToGap n p)
  · intro p hp
    exact PToGap_mem hp
  · intro p hp q hq heq
    have hh := congrArg PFromGap heq
    rw [PFromToGap hp, PFromToGap hq] at hh
    exact hh
  · intro g hg
    exact ⟨PFromGap g, PFromGap_mem hg, PToFromGap hg⟩

theorem PLeftM_card_gap (n : ℕ) : (PLeftM n).card = (PGap n).card := by
  rw [PLeftM_card, PLeftT_card_gap]
