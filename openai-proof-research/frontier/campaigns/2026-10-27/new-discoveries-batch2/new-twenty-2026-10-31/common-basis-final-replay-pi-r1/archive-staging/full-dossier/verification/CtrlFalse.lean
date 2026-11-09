-- Negative control: a False goal. `decide` on a false proposition errors; the
-- compile must exit nonzero.
theorem ctrlFalse : False := by decide
