import Inputs016
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_1400 : CNF.NClause := [(83,false),(4,true),(5,true),(11,true),(17,false),(23,true),(26,true)]
theorem inp_1400 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1400 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1400 (by decide) v h
def cl_1401 : CNF.NClause := [(83,true),(4,false),(5,false),(11,false),(17,true),(23,true),(26,true)]
theorem inp_1401 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1401 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1401 (by decide) v h
def cl_1403 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(17,true),(23,true),(26,true)]
theorem inp_1403 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1403 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1403 (by decide) v h
def cl_1404 : CNF.NClause := [(83,false),(4,true),(5,true),(11,false),(17,true),(23,true),(26,true)]
theorem inp_1404 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1404 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1404 (by decide) v h
def cl_1406 : CNF.NClause := [(83,false),(4,true),(5,false),(11,true),(17,true),(23,true),(26,true)]
theorem inp_1406 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1406 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1406 (by decide) v h
def cl_1407 : CNF.NClause := [(83,false),(4,false),(5,true),(11,true),(17,true),(23,true),(26,true)]
theorem inp_1407 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1407 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1407 (by decide) v h
def cl_1408 : CNF.NClause := [(83,false),(4,true),(5,true),(11,true),(17,true),(23,true),(26,true)]
theorem inp_1408 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1408 := by
  exact input_gate (activationGate5 SatVar.a (.i 21) 21) (activationA_mem 21) cl_1408 (by decide) v h
def cl_1409 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,false),(24,false),(28,false)]
theorem inp_1409 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1409 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1409 (by decide) v h
def cl_1410 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,false),(24,false),(28,false)]
theorem inp_1410 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1410 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1410 (by decide) v h
def cl_1411 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,false),(24,false),(28,false)]
theorem inp_1411 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1411 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1411 (by decide) v h
def cl_1412 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,false),(24,false),(28,false)]
theorem inp_1412 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1412 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1412 (by decide) v h
def cl_1415 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,false),(24,false),(28,false)]
theorem inp_1415 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1415 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1415 (by decide) v h
def cl_1416 : CNF.NClause := [(84,true),(2,true),(5,true),(13,true),(16,false),(24,false),(28,false)]
theorem inp_1416 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1416 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1416 (by decide) v h
def cl_1419 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,true),(24,false),(28,false)]
theorem inp_1419 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1419 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1419 (by decide) v h
def cl_1420 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,true),(24,false),(28,false)]
theorem inp_1420 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1420 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1420 (by decide) v h
def cl_1423 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,true),(24,false),(28,false)]
theorem inp_1423 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1423 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1423 (by decide) v h
def cl_1424 : CNF.NClause := [(84,true),(2,true),(5,true),(13,true),(16,true),(24,false),(28,false)]
theorem inp_1424 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1424 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1424 (by decide) v h
def cl_1427 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,false),(24,true),(28,false)]
theorem inp_1427 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1427 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1427 (by decide) v h
def cl_1428 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,false),(24,true),(28,false)]
theorem inp_1428 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1428 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1428 (by decide) v h
def cl_1431 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,false),(24,true),(28,false)]
theorem inp_1431 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1431 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1431 (by decide) v h
def cl_1435 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,true),(24,true),(28,false)]
theorem inp_1435 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1435 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1435 (by decide) v h
def cl_1436 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,true),(24,true),(28,false)]
theorem inp_1436 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1436 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1436 (by decide) v h
def cl_1439 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,true),(24,true),(28,false)]
theorem inp_1439 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1439 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1439 (by decide) v h
def cl_1440 : CNF.NClause := [(84,false),(2,true),(5,true),(13,true),(16,true),(24,true),(28,false)]
theorem inp_1440 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1440 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1440 (by decide) v h
def cl_1441 : CNF.NClause := [(84,true),(2,false),(5,false),(13,false),(16,false),(24,false),(28,true)]
theorem inp_1441 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1441 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1441 (by decide) v h
def cl_1443 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,false),(24,false),(28,true)]
theorem inp_1443 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1443 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1443 (by decide) v h
def cl_1444 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,false),(24,false),(28,true)]
theorem inp_1444 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1444 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1444 (by decide) v h
def cl_1447 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,false),(24,false),(28,true)]
theorem inp_1447 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1447 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1447 (by decide) v h
def cl_1448 : CNF.NClause := [(84,true),(2,true),(5,true),(13,true),(16,false),(24,false),(28,true)]
theorem inp_1448 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1448 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1448 (by decide) v h
def cl_1451 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,true),(24,false),(28,true)]
theorem inp_1451 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1451 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1451 (by decide) v h
def cl_1452 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,true),(24,false),(28,true)]
theorem inp_1452 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1452 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1452 (by decide) v h
def cl_1455 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,true),(24,false),(28,true)]
theorem inp_1455 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1455 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1455 (by decide) v h
def cl_1456 : CNF.NClause := [(84,false),(2,true),(5,true),(13,true),(16,true),(24,false),(28,true)]
theorem inp_1456 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1456 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1456 (by decide) v h
def cl_1459 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,false),(24,true),(28,true)]
theorem inp_1459 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1459 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1459 (by decide) v h
def cl_1460 : CNF.NClause := [(84,true),(2,true),(5,true),(13,false),(16,false),(24,true),(28,true)]
theorem inp_1460 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1460 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1460 (by decide) v h
def cl_1463 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,false),(24,true),(28,true)]
theorem inp_1463 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1463 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1463 (by decide) v h
def cl_1464 : CNF.NClause := [(84,false),(2,true),(5,true),(13,true),(16,false),(24,true),(28,true)]
theorem inp_1464 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1464 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1464 (by decide) v h
def cl_1467 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(16,true),(24,true),(28,true)]
theorem inp_1467 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1467 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1467 (by decide) v h
def cl_1468 : CNF.NClause := [(84,false),(2,true),(5,true),(13,false),(16,true),(24,true),(28,true)]
theorem inp_1468 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1468 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1468 (by decide) v h
def cl_1470 : CNF.NClause := [(84,false),(2,true),(5,false),(13,true),(16,true),(24,true),(28,true)]
theorem inp_1470 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1470 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1470 (by decide) v h
def cl_1471 : CNF.NClause := [(84,false),(2,false),(5,true),(13,true),(16,true),(24,true),(28,true)]
theorem inp_1471 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1471 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1471 (by decide) v h
def cl_1472 : CNF.NClause := [(84,false),(2,true),(5,true),(13,true),(16,true),(24,true),(28,true)]
theorem inp_1472 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1472 := by
  exact input_gate (activationGate5 SatVar.a (.i 22) 22) (activationA_mem 22) cl_1472 (by decide) v h
def cl_1473 : CNF.NClause := [(85,true),(3,false),(5,false),(12,false),(19,false),(21,false),(27,false)]
theorem inp_1473 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1473 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1473 (by decide) v h
def cl_1474 : CNF.NClause := [(85,true),(3,true),(5,false),(12,false),(19,false),(21,false),(27,false)]
theorem inp_1474 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1474 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1474 (by decide) v h
def cl_1475 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,false),(21,false),(27,false)]
theorem inp_1475 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1475 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1475 (by decide) v h
def cl_1476 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(19,false),(21,false),(27,false)]
theorem inp_1476 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1476 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1476 (by decide) v h
def cl_1477 : CNF.NClause := [(85,true),(3,false),(5,false),(12,true),(19,false),(21,false),(27,false)]
theorem inp_1477 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1477 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1477 (by decide) v h
def cl_1478 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(19,false),(21,false),(27,false)]
theorem inp_1478 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1478 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1478 (by decide) v h
def cl_1479 : CNF.NClause := [(85,true),(3,false),(5,true),(12,true),(19,false),(21,false),(27,false)]
theorem inp_1479 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1479 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1479 (by decide) v h
def cl_1483 : CNF.NClause := [(85,true),(3,false),(5,true),(12,false),(19,true),(21,false),(27,false)]
theorem inp_1483 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_1483 := by
  exact input_gate (activationGate5 SatVar.a (.i 23) 23) (activationA_mem 23) cl_1483 (by decide) v h
end Percolation.Replay
