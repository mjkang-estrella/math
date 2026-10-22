#!/usr/bin/env python3
"""Integrate the Arithmetic159 and Structural192 archives and the Structural193
dispatch into tasks.json on top of the other parent thread's commit 143f03e44f.
The accumulated snapshot is updated in place; every untouched key is asserted equal."""
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
assert len(tasks) == 650, len(tasks)
assert tasks[649]["clientRequestId"] == "twenty-20261022-fresh-arithmetic-r161-codex-astra-r1" and tasks[649]["status"] == "running"
assert tasks[648]["parent_disposition"] == "PREFREEZE_NO_NOMINEE_ARCHIVED"

STATUS_KEYS = ["status", "workState", "hasPendingChildRuns", "latestTerminalRunId", "latestTerminalStatus", "latestTerminalSummary",
               "latestTerminalResultContextTransferId", "summary", "resultContextTransferId", "hasPendingQuestion", "pendingApproval", "waitTimedOut"]


def sha_file(p):
    return hashlib.sha256(open(os.path.join(C, p), "rb").read()).hexdigest()


def archive(idx, cid, pdir, intake_text, asha):
    t = tasks[idx]
    assert t["clientRequestId"] == cid and t["status"] == "running" and t.get("parent_disposition") is None
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
    t["parent_ledger_integration_note"] = ("Intake completed by owner thread 164b1204-be68-4540-94bb-0b91055c4381 before commit d362a37b73/143f03e44f recorded this entry as running under a different owner; "
                                          "ledger integration deferred until the tree was clean and now applied on top of 143f03e44f without altering foreign entries.")


A159_SHA = "23301ee91dcce6db790b0ef72c16c2fa70ab802471ab00c159f7b448311402ce"
S192_SHA = "8c2dbadd49d1af0f08f98b99f98df925c9a18d6fe6e25a611ce91d90fb339eb7"
archive(646, "twenty-20261022-fresh-arithmetic-r159-codex-astra-r1", "discovery-arithmetic-r159-parent",
        "discovery-arithmetic-r159-parent/{task-status.json,replay.py,assessment.md,intake.json,parent-concurrency-note.json}; replay all pass (56 packet files/4510179 B, 67-file root, 11 blobs exhausting the 14-entry folder, 9 include edges, 6 completed-r158 copies, 4 controls rerun, recurrence calculation rerun and parent-rechecked); "
        "unpaid: uniform weighted-area estimate sup over compact K and r<b of the integral of e^{beta' h_t} omega_t over the marked Dloussky-Teleman reference curves C_{t,r} at every supercritical exponent beta'>log rho_K through changing curve configurations including the Enoki branch; zero count", A159_SHA)
archive(647, "twenty-20261022-fresh-structural-r192-codex-astra-r1", "discovery-structural-r192-parent",
        "discovery-structural-r192-parent/{task-status.json,replay.py,assessment.md,intake.json}; replay all pass (97 payload files/5626346 B, 100-file root, 12 blobs exhausting the 14-entry folder, include order verified, 6 completed-r191 copies, 7 history extents, 7 primary PDFs, 4 controls rerun, exterior/transgression/bar scripts rerun and residual identity recomputed by parent); "
        "disclosed guard omission *k369r134-*/*t185r144-* closed prospectively in the r193 brief; unpaid: all-rank, all-floor, all-even-degree quotient Steenrod action and d_3 compatible with the Dickson suspension-ideal inclusions (cokernel = degree-two edge kernel); zero count", S192_SHA)

# --- Structural193 dispatch entry (idx650) ---------------------------------------
disp = json.load(open(os.path.join(C, "discovery-structural-r192-parent/structural-r193-dispatch.json")))
assert disp["clientRequestId"] == "twenty-20261022-fresh-structural-r193-codex-astra-r1" and disp["status"] == "running"
assert sha_file("expanded-target-2026-10-17/fresh-structural-r193-brief.txt") == disp["brief_sha256"]
for i, t in enumerate(tasks):
    assert t.get("clientRequestId") != disp["clientRequestId"], i
tasks.append(copy.deepcopy(disp))
assert len(tasks) == 651

# --- snapshot -------------------------------------------------------------------
s = T["current_work_snapshot"]
s0 = T0["current_work_snapshot"]
assert s["active_task_indices"] == [646, 647] or s["active_task_indices"] == [649] or set(s["active_task_indices"]) <= {646, 647, 649}, s["active_task_indices"]
s["observed_utc"] = NOW
s["active_task_indices"] = [649, 650]
s["t3_last_polled_running"] = [disp["taskId"]]
s["t3_last_polled_running_note"] = ("Own confirmed list for thread 164b1204-be68-4540-94bb-0b91055c4381: Structural193 (idx650) running at dispatch. Arithmetic161 (idx649) is owned by thread 6742db91-d35c-44d0-a762-e5d9232f5177 "
                                    "and cannot be polled from this thread (task_not_found for foreign tasks); its liveness is recorded by its owner only. Arithmetic159 (idx646) and Structural192 (idx647) are completed and archived by their owner, closing the foreign-owner running records.")
s["t3_recorded_running_different_owner"] = [
    {"task_index": 649, "taskId": tasks[649]["taskId"], "parent_thread": "6742db91-d35c-44d0-a762-e5d9232f5177", "shared_record_status": "running",
     "current_thread_status_request": "not_requested_foreign_owner", "current_liveness_verified_here": False,
     "action": "Preserved; no cancellation, duplicate dispatch, requery or live-body/activity inspection. Owner thread archives it."}
]
s["arithmetic159_parent_intake"] = {"disposition": "PREFREEZE_NO_NOMINEE_ARCHIVED", "assessment_sha256": A159_SHA, "intake": "discovery-arithmetic-r159-parent/intake.json", "count_change": 0,
                                    "concurrency_note": "discovery-arithmetic-r159-parent/parent-concurrency-note.json"}
s["structural192_parent_intake"] = {"disposition": "PREFREEZE_NO_NOMINEE_ARCHIVED", "assessment_sha256": S192_SHA, "intake": "discovery-structural-r192-parent/intake.json", "count_change": 0}
s["structural193_prospective_isolation"] = "discovery-structural-r192-parent/prospective-isolation.json"
s["parent_concurrency_2026_10_22"] = {
    "threads": {"164b1204-be68-4540-94bb-0b91055c4381": "owner of idx644-647 and idx650 (MCP command b575b956-eb20-481c-b9de-822c8efa824c)",
                "6742db91-d35c-44d0-a762-e5d9232f5177": "owner of idx648-649 (MCP command eabfe867-92ae-4600-a4b7-dec665823dc7); commits d362a37b73, 143f03e44f"},
    "rule": "Each thread integrates only tasks it owns; foreign entries are never replaced, polled, cancelled or inspected; ledgers re-read immediately before every write; no acceptance/count change by either thread.",
    "structural193_brief_peer_naming": "The Structural193 brief (composed before 143f03e44f was observed) names Arithmetic160 as the sole live peer; at dispatch Arithmetic160 was already archived and Arithmetic161 (idx649, Source063) was live. Structural193's inherited supplement line carries *arithmetic*r161* and the standing brief excludes all active rounds; Arithmetic161's original brief carries *structural*r193*. Mutual prospective guards therefore hold; the stale peer name is a disclosed wording defect, not an isolation gap.",
}
s["note"] = ("Arithmetic159 (idx646, Source060) and Structural192 (idx647, Source316) completed PREFREEZE/no nominee and archived by their owner thread: the uniform supercritical weighted-area estimate for the marked Dloussky-Teleman reference curves, and the all-rank all-floor quotient Steenrod action with compatible d_3, remain unpaid respectively. "
             "Replays all pass; no theorem frozen, no grade, no acceptance/count change. Structural193 (idx650, Source317 Thomason model structures in all strict higher dimensions) dispatched with Astra high/default. "
             "Arithmetic161 (idx649) remains live under thread 6742db91 and is not polled here; Arithmetic160 archive (idx648) preserved untouched. Campaign 19/20, latest R041, one remains; publication STOPPED.")
T["last_parent_progress"] = s["note"]

# --- invariants ---------------------------------------------------------------------
CH = {"observed_utc", "active_task_indices", "t3_last_polled_running", "t3_last_polled_running_note", "t3_recorded_running_different_owner", "note",
      "arithmetic159_parent_intake", "structural192_parent_intake", "structural193_prospective_isolation", "parent_concurrency_2026_10_22"}
for k in s0:
    if k not in CH:
        assert s[k] == s0[k], k
assert set(s0) - CH <= set(s)
for i in range(650):
    if i not in (646, 647):
        assert tasks[i] == T0["tasks"][i], i
for k in T0:
    if k not in ("tasks", "current_work_snapshot", "last_parent_progress"):
        assert T[k] == T0[k], k
assert tasks[648]["parent_thread"] == "6742db91-d35c-44d0-a762-e5d9232f5177"
open(TS, "w").write(json.dumps(T, indent=2) + "\n")
print(json.dumps({"tasks": len(tasks), "idx650": tasks[650]["clientRequestId"], "active": s["active_task_indices"], "utc": NOW}))
