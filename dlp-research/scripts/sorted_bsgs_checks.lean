import Research.SortedBSGS

/-! Compiled execution checks, not proof-producing native evaluation. All
formal claims are separately proved and audited in the Research modules. -/
open Research

#eval do
  for m in [1, 3, 7, 8] do
    let mut maxQueries := 0
    let mut maxProbes := 0
    let mut maxComparisons := 0
    for d in List.range 7 do
      let result := SortedBSGS.solve SmallCurve.problem OrbitRefinement.smallCurve
        PointKeys.smallCurve m (SmallCurve.multiple d)
      if result.answer != some d then
        throw (IO.userError s!"wrong scalar: m={m}, d={d}, result={repr result}")
      let blocks := BSGSArithmetic.blockCount 7 m
      let probeBound := blocks * IndexedLookup.fuelFor m
      if result.queries > blocks || result.probes > probeBound ||
          result.comparisonCalls > 2 * probeBound then
        throw (IO.userError s!"counter bound failed: m={m}, d={d}")
      maxQueries := max maxQueries result.queries
      maxProbes := max maxProbes result.probes
      maxComparisons := max maxComparisons result.comparisonCalls
    IO.println s!"m={m} cases=7 maxQueries={maxQueries} maxProbes={maxProbes} maxComparisonCalls={maxComparisons}"
  IO.println "PASS: all 28 full-range scalar/width cases. Query counters only; preprocessing and other work excluded."
