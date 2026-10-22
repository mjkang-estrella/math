#!/usr/bin/env python3
"""Integrate the Structural193 archive and the Structural194 dispatch into tasks.json
on top of the other parent thread's commit 2789cbceb8 (Arithmetic161 archived, Arithmetic162
dispatched there). The accumulated snapshot is updated in place; every untouched key is asserted equal."""
import copy
import datetime
import hashlib
import json
import os

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NOW = datetime.datetime.now(datetime.timezone.utc).isoformat()
TS = os.path.join(C, "tasks.json")
T = json.load(open(TS))
T0 = copy.deepcopy(T)
tasks = T["tasks"]
assert len(tasks) == 652, len(tasks)
assert tasks[651]["clientRequestId"] == "twenty-20261022-fresh-arithmetic-r162-codex-astra-r1" and tasks[651]["status"] == "running"
assert tasks[651]["parent_thread"] == "6742db91-d35c-44d0-a762-e5d9232f5177"
assert tasks[649]["parent_disposition"] == "PREFREEZE_NO_NOMINEE_ARCHIVED"
assert tasks[648]["parent_disposition"] == "PREFREEZE_NO_NOMINEE_ARCHIVED"

STATUS_KEYS = ["status", "workState", "hasPendingChildRuns", "latestTerminalRunId", "latestTerminalStatus", "latestTerminalSummary",
               "latestTerminalResultContextTransferId", "summary", "resultContextTransferId", "hasPendingQuestion", "pendingApproval", "waitTimedOut"]


def sha_file(p):
    return hashlib.sha256(open(os.path.join(C, p), "rb").read()).hexdigest()


def archive(idx, cid, pdir, intake_text, asha):
    t = tasks[idx]
    assert t["clientRequestId"] == cid and t["status"] == "running" and t.get("parent_disposition") is None
    assert t["parent_thread"] == "164b1204-be68-4540-94bb-0b91055c4381"
    st = json.load(open(os.path.join(C, pdir, "task-status.json")))
    assert st["taskId"] == t["taskId"] and st["status"] == "completed" and st["latestTerminalStatus"] == "completed"
    for k in STATUS_KEYS:
        t[k] = st[k]
    ik = json.load(open(os.path.join(C, pdir, "intake.json")))
    assert ik["task_index"] == idx and ik["assessment_sha256"] == asha and ik["parent_disposition"] == "PREFREEZE_NO_NOMINEE_ARCHIVED"
    assert sha_file(pdir + "/assessment.md") == asha
    t["parent_disposition"] = "PREFREEZE_NO_NOMINEE_ARCHIVED"
    t["parent_full_intake_pending"] = False
    t["parent_intake"] = intake_text
    t["parent_assessment_sha256"] = asha
    t["parent_intake_utc"] = ik["observed_utc"]
    t["parent_ledger_integration_utc"] = NOW
    t["parent_ledger_integration_note"] = ("Intake completed by owner thread 164b1204-be68-4540-94bb-0b91055c4381 while commit 2789cbceb8 (thread 6742db91) recorded this entry as running under a different owner; "
                                          "ledger integration applied on top of 2789cbceb8 without altering foreign entries.")


S193_SHA = "11020f2e66de8143ab588aa32160a271008d2c34aab9676bff842308a0159be0"
archive(650, "twenty-20261022-fresh-structural-r193-codex-astra-r1", "discovery-structural-r193-parent",
        "discovery-structural-r193-parent/{task-status.json,replay.py,assessment.md,intake.json}; replay all pass (94 payload files/10269462 B, 97-file root, 13 blobs exhausting the 15-entry folder, 10 include edges reparsed with the appendix order 09 then 08, 12 text blobs fully read and the PDF authenticated only, 6 completed-r192 copies, 6 history extents, 6 primary PDFs, 4 controls rerun, chain_calculation.py rerun identical; "
        "parent independent poset-nerve-model rechecks: overlap-corrected recursion dh+hd=id on 1102 simplices of 60 random retract-sieve posets, square-zero normalization, norm recurrence, filler identity, two-stage perturbation contraction, exhaustive diamond obstruction with zero single-cylinder solutions, prepend contraction on 20 posets); "
        "unpaid (DERIVATIONS section 11): positive strict realization of the signed overlap-corrected normalized Street-nerve-chain data as stationary RIGHT Gray-cylinder zigzags between id_Y and j p_r under U_n(A) in every dimension including omega, respecting globular boundaries, lower Steiner-table entries and guarded compositions/equalities, with coherent finite-piece realization over the small-poset diagram; "
        "disclosed brief wording defect (Arithmetic160 named as live peer while Arithmetic161 was live; mutual guards held); zero count", S193_SHA)

# --- Structural194 dispatch entry (idx652) ---------------------------------------
disp = json.load(open(os.path.join(C, "discovery-structural-r193-parent/structural-r194-dispatch.json")))
assert disp["clientRequestId"] == "twenty-20261022-fresh-structural-r194-codex-astra-r1" and disp["status"] == "running"
assert sha_file("expanded-target-2026-10-17/fresh-structural-r194-brief.txt") == disp["brief_sha256"]
assert os.path.getsize(os.path.join(C, "expanded-target-2026-10-17/fresh-structural-r194-brief.txt")) == disp["brief_bytes"]
for i, t in enumerate(tasks):
    assert t.get("clientRequestId") != disp["clientRequestId"], i
tasks.append(copy.deepcopy(disp))
assert len(tasks) == 653

# --- snapshot -------------------------------------------------------------------
s = T["current_work_snapshot"]
s0 = T0["current_work_snapshot"]
assert set(s["active_task_indices"]) <= {649, 650, 651}, s["active_task_indices"]
s["observed_utc"] = NOW
s["active_task_indices"] = [651, 652]
s["t3_last_polled_running"] = [disp["taskId"]]
s["t3_last_polled_running_note"] = ("Own confirmed list for thread 164b1204-be68-4540-94bb-0b91055c4381: Structural194 (idx652) running at dispatch. Arithmetic162 (idx651) is owned by thread 6742db91-d35c-44d0-a762-e5d9232f5177 "
                                    "and cannot be polled from this thread (task_not_found for foreign tasks); its liveness is recorded by its owner only. Structural193 (idx650) is completed and archived by its owner, closing the foreign-owner running record left at 2789cbceb8. "
                                    "The stale active_task_indices [649,650] recorded at 2789cbceb8 (Arithmetic161 already archived there) is corrected to [651,652].")
s["t3_recorded_running_different_owner"] = [
    {"task_index": 651, "taskId": tasks[651]["taskId"], "parent_thread": "6742db91-d35c-44d0-a762-e5d9232f5177", "shared_record_status": "running",
     "current_thread_status_request": "not_requested_foreign_owner", "current_liveness_verified_here": False,
     "action": "Preserved; no cancellation, duplicate dispatch, requery or live-body/activity inspection. Owner thread archives it."}
]
s["structural193_parent_intake"] = {"disposition": "PREFREEZE_NO_NOMINEE_ARCHIVED", "assessment_sha256": S193_SHA, "intake": "discovery-structural-r193-parent/intake.json", "count_change": 0}
s["structural194_prospective_isolation"] = "discovery-structural-r193-parent/prospective-isolation.json"
pc = s["parent_concurrency_2026_10_22"]
assert set(pc) == {"threads", "rule", "structural193_brief_peer_naming"}, set(pc)
pc["threads"] = {"164b1204-be68-4540-94bb-0b91055c4381": "owner of idx644-647, idx650 and idx652 (MCP command b575b956-eb20-481c-b9de-822c8efa824c); commits 21adb9f132, 775042d295, 8a57365802 and this one",
                 "6742db91-d35c-44d0-a762-e5d9232f5177": "owner of idx648, idx649 and idx651 (MCP command eabfe867-92ae-4600-a4b7-dec665823dc7); commits d362a37b73, 143f03e44f, 2789cbceb8"}
pc["structural194_brief_peer_naming"] = ("The Structural194 brief names Arithmetic162 (idx651) as the sole live peer, which was the live foreign task at dispatch (2789cbceb8 observed before composition). "
                                         "Arithmetic162's original brief carries *structural*r194*; the Structural194 supplement line carries *arithmetic*r160* through *arithmetic*r165*. Mutual prospective guards hold.")
s["note"] = ("Structural193 (idx650, Source317 Thomason model structures in all strict higher dimensions) completed PREFREEZE/no nominee and archived by its owner thread: positive strict realization of the signed overlap-corrected Street-nerve chain contraction as stationary RIGHT Gray-cylinder zigzags in every dimension with coherent finite-piece realization remains unpaid. "
             "Replay all pass and parent independent poset-model finite rechecks; no theorem frozen, no grade, no acceptance/count change. Structural194 (idx652, Source318 chromatic splitting filtrations and counterexamples, five manuscripts/85 blobs) dispatched with Astra high/default. "
             "Arithmetic162 (idx651) remains live under thread 6742db91 and is not polled here; Arithmetic160/161 archives (idx648/649) preserved untouched. Campaign 19/20, latest R041, one remains; publication STOPPED.")
T["last_parent_progress"] = s["note"]

# --- invariants ---------------------------------------------------------------------
CH = {"observed_utc", "active_task_indices", "t3_last_polled_running", "t3_last_polled_running_note", "t3_recorded_running_different_owner", "note",
      "structural193_parent_intake", "structural194_prospective_isolation", "parent_concurrency_2026_10_22"}
for k in s0:
    if k not in CH:
        assert s[k] == s0[k], k
assert set(s0) - CH <= set(s)
assert pc["rule"] == s0["parent_concurrency_2026_10_22"]["rule"]
assert pc["structural193_brief_peer_naming"] == s0["parent_concurrency_2026_10_22"]["structural193_brief_peer_naming"]
for i in range(652):
    if i != 650:
        assert tasks[i] == T0["tasks"][i], i
for k in T0:
    if k not in ("tasks", "current_work_snapshot", "last_parent_progress"):
        assert T[k] == T0[k], k
assert T["newAccepted"] == 19 and T["latestAcceptance"] == "R041" and T["remaining"] == 1
open(TS, "w").write(json.dumps(T, indent=2) + "\n")
print(json.dumps({"tasks": len(tasks), "idx652": tasks[652]["clientRequestId"], "idx650": tasks[650]["parent_disposition"], "active": s["active_task_indices"], "utc": NOW}))
