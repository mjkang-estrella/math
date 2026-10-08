import Research

def main : IO Unit := do
  IO.println "DLP research specification compiled."
  IO.println "Verified: machine checks, finite coordinate curve, exhaustive and sorted BSGS correctness, indexed-query comparison bounds, encoding audits, secp256k1 generator equation, capacity arithmetic."
  IO.println "OPEN: cryptographic EC refinement, hard family, full preprocessing/arithmetic/memory costs, tape solver, realistic calibration, faster candidate."
  IO.println "This executable checks artifacts; it does not launch research agents. No cryptographic breakthrough is claimed."
