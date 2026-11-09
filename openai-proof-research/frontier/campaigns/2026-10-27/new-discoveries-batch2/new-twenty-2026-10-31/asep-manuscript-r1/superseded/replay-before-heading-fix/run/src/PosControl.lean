import ASEPCheck

/-! Positive control (expected to SUCCEED): the first stored certificate passes the checker. -/

open ASEP

example : chk (decode (certChunk0.headD 0)) = true := by decide +kernel
