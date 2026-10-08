import Research.WordRun

/-! Fresh-run accounting consequences of the accepted word interpreter.
These abstract action counts imply no solver, hardware, bit or tape bound. -/
namespace Research.WordRunFacts

open Research.WordCore Research.WordRun

/-- Once execution enters the guest phase, it emits only actual guest events. -/
theorem guest_trace {P : Profile} (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) (s : State P) :
    ∀ e ∈ (continueRun code input fuel (.guest s)).trace, isGuest e = true := by
  induction fuel generalizing s with
  | zero => simp [continueRun, normalize]
  | succ fuel ih =>
    simp only [continueRun, normalize]
    cases h : (WordCore.step code s).outcome with
    | continued next =>
      simp only [prepend, List.mem_cons]
      intro e he
      rcases he with rfl | he
      · rfl
      · exact ih next e he
    | halted next => simp [isGuest]
    | faulted reason next => simp [isGuest]

private theorem no_setup_counts {P : Profile} (trace : List (WordRun.Event P))
    (h : ∀ e ∈ trace, isGuest e = true) :
    (ledgerOf trace).clearRegisters = 0 ∧ (ledgerOf trace).clearHeap = 0 ∧
      (ledgerOf trace).inputCopies = 0 := by
  induction trace with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons e es ih =>
    have he := h e (by simp)
    have ht : ∀ x ∈ es, isGuest x = true := by intro x hx; exact h x (by simp [hx])
    have hi := ih ht
    cases e <;> simp_all [isGuest, ledgerOf, List.countP_cons,
      isRegisterClear, isHeapClear, isInputCopy]

theorem guest_setup_counts {P : Profile} (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) (s : State P) :
    (continueRun code input fuel (.guest s)).ledger.clearRegisters = 0 ∧
    (continueRun code input fuel (.guest s)).ledger.clearHeap = 0 ∧
    (continueRun code input fuel (.guest s)).ledger.inputCopies = 0 :=
  no_setup_counts _ (guest_trace code input fuel s)

/-- Every fresh run with enough setup fuel pays each setup action exactly once,
regardless of later halt, fault or exhaustion. -/
theorem run_setup_counts (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (extra : Nat) :
    (run P code input (setupUnits P + extra)).ledger.clearRegisters = P.R ∧
    (run P code input (setupUnits P + extra)).ledger.clearHeap = P.M ∧
    (run P code input (setupUnits P + extra)).ledger.inputCopies = P.L := by
  rw [run_setup_boundary]
  have hs := completeSetup_counts P input
  have hg := guest_setup_counts code input extra (initialized P input)
  simp only [Result.ledger, ledgerOf, prependTrace, List.countP_append] at hs hg ⊢
  omega

theorem run_setup_units (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (extra : Nat) : (run P code input (setupUnits P + extra)).ledger.setupUnits = setupUnits P := by
  have h := run_setup_counts P code input extra
  simp only [Ledger.setupUnits]
  rw [h.1, h.2.1, h.2.2]
  rfl

/-- A terminal result cannot occur while initialization is incomplete. -/
theorem terminal_setup_fuel (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) (h : (run P code input fuel).stop.Terminal) : setupUnits P ≤ fuel := by
  by_cases hf : fuel < setupUnits P
  · rw [run_before_setup P code input fuel hf] at h
    exact False.elim h
  · omega

theorem terminal_setup_counts (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) (h : (run P code input fuel).stop.Terminal) :
    (run P code input fuel).ledger.setupUnits = setupUnits P := by
  have hf := terminal_setup_fuel P code input fuel h
  have he : fuel = setupUnits P + (fuel - setupUnits P) := by omega
  rw [he]
  exact run_setup_units P code input (fuel - setupUnits P)

/-- Both successful and faulting fresh runs must pay the entire raw setup. -/
theorem terminal_pays_setup (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) (h : (run P code input fuel).stop.Terminal) :
    setupUnits P ≤ (run P code input fuel).used := by
  have he := ledger_used (run P code input fuel).trace
  change (run P code input fuel).used = (run P code input fuel).ledger.setupUnits +
    (run P code input fuel).ledger.guestAttempts at he
  rw [terminal_setup_counts P code input fuel h] at he
  omega

/-- Exact total/guest decomposition for a fresh terminal run. -/
theorem terminal_used (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) (h : (run P code input fuel).stop.Terminal) :
    (run P code input fuel).used = setupUnits P + (run P code input fuel).ledger.guestAttempts := by
  have he := ledger_used (run P code input fuel).trace
  change (run P code input fuel).used = (run P code input fuel).ledger.setupUnits +
    (run P code input fuel).ledger.guestAttempts at he
  rwa [terminal_setup_counts P code input fuel h] at he

/-- With identical raw setup, total and guest attempt orderings coincide.
Both results must be terminal; this says nothing about correctness or speed. -/
theorem terminal_ordering (P : Profile) (a b : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) (ha : (run P a input fuel).stop.Terminal)
    (hb : (run P b input fuel).stop.Terminal) :
    (run P a input fuel).used ≤ (run P b input fuel).used ↔
      (run P a input fuel).ledger.guestAttempts ≤ (run P b input fuel).ledger.guestAttempts := by
  rw [terminal_used P a input fuel ha, terminal_used P b input fuel hb]
  omega

/-- A guest segment split is justified by the actual exhausted continuation
state, not by inventing PC fields in an opcode-only event trace. -/
theorem guest_split {P : Profile} (code : Program P) (input : Fin P.L → Bool)
    (a b : Nat) (s mid : State P)
    (h : (continueRun code input a (.guest s)).stop = .exhausted (.guest mid)) :
    continueRun code input (a + b) (.guest s) =
      prependTrace (continueRun code input a (.guest s)).trace
        (continueRun code input b (.guest mid)) := by
  induction a generalizing s with
  | zero =>
    simp only [continueRun, normalize, Stop.exhausted.injEq, Phase.guest.injEq] at h
    subst mid
    simp [continueRun, normalize, prependTrace]
  | succ a ih =>
    simp only [Nat.succ_add, continueRun, normalize] at h ⊢
    cases he : (WordCore.step code s).outcome with
    | continued next =>
      simp only [he, prepend] at h ⊢
      rw [ih next h]
      rfl
    | halted next => simp [he] at h
    | faulted reason next => simp [he] at h

end Research.WordRunFacts
