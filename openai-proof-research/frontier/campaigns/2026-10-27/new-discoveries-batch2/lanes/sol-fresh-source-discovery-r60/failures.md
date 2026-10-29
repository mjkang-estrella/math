# Retained failures and access limits

* First source_audit.py (then named inspect.py) attempted unavailable bs4; fixed to stdlib regex/html extraction. No installation. Original failure is in tool transcript; source-audit logs retained.
* inspect.py shadowed Python stdlib inspect and caused the first mathematical script import to fail; renamed source_audit.py. check-failed-import.log retained.
* Initial SymPy interpolation used ZZ for rational ground multiplication; fixed explicitly to QQ. check-failed-domain.log retained.
* First routes.py definition loader omitted __file__; fixed; routes-failed.log retained.
* deep-incomplete run hit the RLIMIT_CPU ceiling: -9 at approximately210.6 wall seconds,195 completed cases persisted. The monitor reports reason=null because the kernel killed the child at its CPU limit, before monitor action. No PASS for the incomplete whole run. Reduced workload in deep.py completed separately; no cap increase.
* Larger moment run may be incomplete; authoritative status is its guard and provenance, not existence of partial JSON. See final summary.
* Journal article route redirected to /math/login despite HTTP200. This is an access failure for the article body. No account/login operation or bypass attempted.
* GitHubAPI shared403 inherited, no retry. Live raw README is not a complete registry refresh. FreshnessHOLD persists. Cached Blueprint/D5 path inventory is not Lean D5 and is not a cross-format byte-delta proof.

Final larger moment receipt: kernel CPU cap exit-9 at210.55wall seconds,33 completed cases through dimension23 persisted. Not a completed PASS. Restored the runnable moment suite to the successful80 cases through12. All incomplete results remain explicitly partial. No unsampled-transient memory guarantee is claimed by the40ms RSS sampler.

The original larger workloads are retained as deep-large.py and moments-large.py, writing separate replay filenames. They are NOT in the successful run.sh suite. If reproducing those failures, invoke only through `python capped_run.py python deep-large.py` or `python capped_run.py python moments-large.py`; do not run them uncapped. They were not rerun after reaching the cap.
