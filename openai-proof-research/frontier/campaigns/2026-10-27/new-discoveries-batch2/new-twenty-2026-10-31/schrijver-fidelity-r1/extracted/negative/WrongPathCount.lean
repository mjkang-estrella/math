import PathCoverage
set_option maxRecDepth 20000
example : (Schrijver.endMasks 27 12).length = 820 := by decide +kernel
