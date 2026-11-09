All commands run from this lane. Prefix every Python invocation with:

`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py`

Run `python package.py prepare`, `python package.py archive`, then `python package.py replay` under that guard. The extracted replay compiles Literal, InstanceG, InstanceH, Geometry, Inventory and Audit serially using the pinned compiler and nine packages. Helpers keep AS/group RSS512MiB CPU210 wall230. The existing runner starts Lean in a distinct session under the explicitly authorized serial exception, j1 M2700 groupRSS2800MiB CPU210 wall230, warningAsError=true, autoImplicit=false. Its AS is unlimited as in the inherited runner, with Lean's M2700 allocation cap and the external groupRSS limit; no helper cap is raised.

The archive intentionally contains only proved modules and the complete origin audit. RationalEnumeration.lean is a failed experimental candidate outside the proved archive; its declarations are not imported or credited. Preserve attempt logs. Finalize with `python finalize.py` and a separate `python verify.py`, each guarded. No owned compiled artifacts remain after replay.
