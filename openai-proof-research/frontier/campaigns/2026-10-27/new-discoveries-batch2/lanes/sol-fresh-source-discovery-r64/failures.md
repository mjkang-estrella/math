# Retained failures and corrections

1. `failure-transfer-index.json`: IndexError when reading a nonconstant coefficient of the zero-th matrix power represented by a length-one list. Fixed by explicit zero padding; caps unchanged.
2. `failure-bridge-import.json`: the shared-function exec environment lacked __file__. Fixed by supplying the local script name; caps unchanged.
3. `diagnostic-before-golden-correction.json`: preliminary golden full transfer used only the dual-number word lifted linearly, which is insufficient for full jets. Reading actual UnboundedGolden.lean gave the degree-one exceptional step k=1,D=1+x-x^2; fixed from this primary body. Original diagnostic retained, superseded. Final golden cycle degree weight4; n>=2 unchanged. No theorem claim made from the original lift.
