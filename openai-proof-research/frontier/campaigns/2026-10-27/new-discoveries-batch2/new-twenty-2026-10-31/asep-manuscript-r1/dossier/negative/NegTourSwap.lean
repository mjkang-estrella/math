import ASEPCheck

/-! Negative control (expected to FAIL): the direction of the first certificate paired with the cyclic
order and successor list of the second certificate; the support test must reject it. -/

open ASEP

example : chk { decode (certChunk0.headD 0) with
    tl := (decode (certChunk0.getD 1 0)).tl, s := (decode (certChunk0.getD 1 0)).s } = true := by
  decide +kernel
