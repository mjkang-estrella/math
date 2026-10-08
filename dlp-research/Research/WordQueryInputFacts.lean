import Research.WordPacking

/-! Index-level associations for the actual W016 source bit buffer. These
lemmas neither execute a guest load nor assume a packed/initialized guest state.
No replacement encoding, decoder implementation, or cost claim is supplied. -/
namespace Research.WordQueryInputFacts

open WordQueryData WordPacking

theorem m_index_bound (s : Sizes) (i : Nat) (hi : i < s.W) : i < s.L := by
  unfold Sizes.L
  omega

theorem k_index_bound (s : Sizes) (i : Nat) (hi : i < s.W) : s.W + i < s.L := by
  unfold Sizes.L
  omega

/-- The exact source record end precedes the query, independent of numerical
code admission. This is a bit-list offset fact, not a guest word bound. -/
theorem record_end_bound (s : Sizes) (j : Fin s.m) :
    s.recordStart j.val + s.k + s.W ≤ s.queryStart := by
  have hj : j.val + 1 ≤ s.m := by have := j.isLt; omega
  have hp := Nat.mul_le_mul_right (s.k + s.W) hj
  simp only [Nat.add_mul, Nat.one_mul] at hp
  unfold Sizes.recordStart Sizes.queryStart
  omega

theorem key_index_bound (s : Sizes) (j : Fin s.m) (i : Nat) (hi : i < s.k) :
    s.recordStart j.val + i < s.L := by
  have he := record_end_bound s j
  unfold Sizes.queryStart Sizes.L at *
  omega

theorem payload_index_bound (s : Sizes) (j : Fin s.m) (i : Nat) (hi : i < s.W) :
    s.recordStart j.val + s.k + i < s.L := by
  have he := record_end_bound s j
  unfold Sizes.queryStart Sizes.L at *
  omega

theorem query_index_bound (s : Sizes) (i : Nat) (hi : i < s.k) :
    s.queryStart + i < s.L := by
  unfold Sizes.queryStart Sizes.L
  omega

private theorem entries_index_bound {s : Sizes} (es : List (Entry s))
    (j i : Nat) (hj : j < es.length) (hi : i < s.k + s.W) :
    j * (s.k + s.W) + i < (encodeEntries es).length := by
  rw [encodeEntries_length]
  have hp := Nat.mul_le_mul_right (s.k + s.W) (show j + 1 ≤ es.length by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hp
  omega

private theorem entries_getElem? {s : Sizes} (es : List (Entry s))
    (j i : Nat) (hj : j < es.length) (hi : i < s.k + s.W) :
    (encodeEntries es)[j * (s.k + s.W) + i]? = (encodeEntry es[j])[i]? := by
  induction es generalizing j with
  | nil => simp at hj
  | cons e es ih =>
    cases j with
    | zero =>
      simp only [encodeEntries, List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      exact List.getElem?_append_left (by rw [encodeEntry_length]; exact hi)
    | succ j =>
      have hj' : j < es.length := by simp only [List.length_cons] at hj; omega
      have hb : (encodeEntry e).length ≤ (j + 1) * (s.k + s.W) + i := by
        rw [encodeEntry_length, Nat.add_mul, Nat.one_mul]
        omega
      simp only [encodeEntries, List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right hb]
      have he : (j + 1) * (s.k + s.W) + i - (encodeEntry e).length = j * (s.k + s.W) + i := by
        rw [encodeEntry_length, Nat.add_mul, Nat.one_mul]
        omega
      rw [he]
      exact ih j hj'

private theorem raw_of_getElem? {s : Sizes} (d : Data s) (n : Nat) (hn : n < s.L)
    (b : Bool) (h : (encode d)[n]? = some b) : rawInput d ⟨n, hn⟩ = b := by
  have hl : n < (encode d).length := by rw [encode_length]; exact hn
  rw [List.getElem?_eq_getElem hl] at h
  exact Option.some.inj h

private theorem encoded_bit {width value i : Nat} (hi : i < width) :
    (Research.bits width value)[i]? = some (bitValue value i == 1) := by
  rw [List.getElem?_eq_getElem (by rw [bits_length]; exact hi), bits_getElem _ _ _ hi]

/-- Header bit association needs no admission. Recovering the complete header
value additionally requires the existing numerical `header_bounds` theorem;
these index facts alone do not exclude truncation outside admitted sizes. -/
theorem raw_m_bit {s : Sizes} (d : Data s) (i : Nat) (hi : i < s.W) :
    rawInput d ⟨i, m_index_bound s i hi⟩ = (bitValue s.m i == 1) := by
  apply raw_of_getElem?
  simp only [encode, tableBits, List.append_assoc]
  rw [List.getElem?_append_left (by rw [bits_length]; exact hi)]
  exact encoded_bit hi

theorem raw_k_bit {s : Sizes} (d : Data s) (i : Nat) (hi : i < s.W) :
    rawInput d ⟨s.W + i, k_index_bound s i hi⟩ = (bitValue s.k i == 1) := by
  apply raw_of_getElem?
  simp only [encode, tableBits, List.append_assoc]
  rw [List.getElem?_append_right (by rw [bits_length]; omega)]
  simp only [bits_length, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by rw [bits_length]; exact hi)]
  exact encoded_bit hi

private theorem record_encoded_getElem? {s : Sizes} (d : Data s) (j : Fin s.m)
    (i : Nat) (hi : i < s.k + s.W) :
    (encode d)[s.recordStart j.val + i]? = (encodeEntry (d.entries.get j))[i]? := by
  simp only [encode, tableBits, List.append_assoc, Sizes.recordStart]
  rw [List.getElem?_append_right (by rw [bits_length]; omega)]
  simp only [bits_length]
  have he : 2 * s.W + j.val * (s.k + s.W) + i - s.W =
      s.W + (j.val * (s.k + s.W) + i) := by omega
  rw [he, List.getElem?_append_right (by rw [bits_length]; omega)]
  simp only [bits_length, Nat.add_sub_cancel_left]
  have hj : j.val < d.entries.toList.length := by rw [Vector.length_toList]; exact j.isLt
  rw [List.getElem?_append_left (entries_index_bound d.entries.toList j.val i hj hi)]
  simpa [Vector.get] using entries_getElem? d.entries.toList j.val i hj hi

theorem raw_key_bit {s : Sizes} (d : Data s) (j : Fin s.m) (i : Nat) (hi : i < s.k) :
    rawInput d ⟨s.recordStart j.val + i, key_index_bound s j i hi⟩ =
      (bitValue (d.entries.get j).key.val i == 1) := by
  apply raw_of_getElem?
  rw [record_encoded_getElem? d j i (by omega)]
  unfold encodeEntry
  rw [List.getElem?_append_left (by rw [bits_length]; exact hi)]
  exact encoded_bit hi

theorem raw_payload_bit {s : Sizes} (d : Data s) (j : Fin s.m) (i : Nat) (hi : i < s.W) :
    rawInput d ⟨s.recordStart j.val + s.k + i, payload_index_bound s j i hi⟩ =
      (bitValue (d.entries.get j).payload.val i == 1) := by
  apply raw_of_getElem?
  rw [Nat.add_assoc, record_encoded_getElem? d j (s.k + i) (by omega)]
  unfold encodeEntry
  rw [List.getElem?_append_right (by rw [bits_length]; omega)]
  simp only [bits_length, Nat.add_sub_cancel_left]
  exact encoded_bit hi

theorem raw_query_bit {s : Sizes} (d : Data s) (i : Nat) (hi : i < s.k) :
    rawInput d ⟨s.queryStart + i, query_index_bound s i hi⟩ =
      (bitValue d.query.val i == 1) := by
  apply raw_of_getElem?
  unfold encode
  rw [List.getElem?_append_right (by rw [tableBits_length]; omega)]
  simp only [tableBits_length, Nat.add_sub_cancel_left]
  exact encoded_bit hi

theorem raw_m_value {s : Sizes} (d : Data s) (i : Nat) (hi : i < s.W) :
    (if rawInput d ⟨i, m_index_bound s i hi⟩ then 1 else 0) = bitValue s.m i := by
  rw [raw_m_bit d i hi]
  exact bitValue_bool s.m i

theorem raw_k_value {s : Sizes} (d : Data s) (i : Nat) (hi : i < s.W) :
    (if rawInput d ⟨s.W + i, k_index_bound s i hi⟩ then 1 else 0) = bitValue s.k i := by
  rw [raw_k_bit d i hi]
  exact bitValue_bool s.k i

theorem raw_key_value {s : Sizes} (d : Data s) (j : Fin s.m) (i : Nat) (hi : i < s.k) :
    (if rawInput d ⟨s.recordStart j.val + i, key_index_bound s j i hi⟩ then 1 else 0) =
      bitValue (d.entries.get j).key.val i := by
  rw [raw_key_bit d j i hi]
  exact bitValue_bool _ i

theorem raw_payload_value {s : Sizes} (d : Data s) (j : Fin s.m) (i : Nat) (hi : i < s.W) :
    (if rawInput d ⟨s.recordStart j.val + s.k + i, payload_index_bound s j i hi⟩ then 1 else 0) =
      bitValue (d.entries.get j).payload.val i := by
  rw [raw_payload_bit d j i hi]
  exact bitValue_bool _ i

theorem raw_query_value {s : Sizes} (d : Data s) (i : Nat) (hi : i < s.k) :
    (if rawInput d ⟨s.queryStart + i, query_index_bound s i hi⟩ then 1 else 0) =
      bitValue d.query.val i := by
  rw [raw_query_bit d i hi]
  exact bitValue_bool _ i

end Research.WordQueryInputFacts
