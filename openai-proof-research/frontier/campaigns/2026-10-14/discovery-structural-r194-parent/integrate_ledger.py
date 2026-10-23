#!/usr/bin/env python3
"""Integrate the Structural194 archive and the Structural195 dispatch into tasks.json
on top of the other parent thread's commit e2a071e5d3 (Arithmetic162/162b archived, Arithmetic162c
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
OWN = "164b1204-be68-4540-94bb-0b91055c4381"
OTHER = "6742db91-d35c-44d0-a762-e5d9232f5177"
assert len(tasks) == 655, len(tasks)
assert tasks[654]["clientRequestId"] == "twenty-20261022-fresh-arithmetic-r162c-codex-astra-r1" and tasks[654]["status"] == "running"
assert tasks[654]["parent_thread"] == OTHER
for i in (648, 649, 651, 653):
    assert tasks[i]["parent_disposition"] == "PREFREEZE_NO_NOMINEE_ARCHIVED" and tasks[i]["parent_thread"] == OTHER, i
assert tasks[650]["parent_disposition"] == "PREFREEZE_NO_NOMINEE_ARCHIVED" and tasks[650]["parent_thread"] == OWN

STATUS_KEYS = ["status", "workState", "hasPendingChildRuns", "latestTerminalRunId", "latestTerminalStatus", "latestTerminalSummary",
               "latestTerminalResultContextTransferId", "summary", "resultContextTransferId", "hasPendingQuestion", "pendingApproval", "waitTimedOut"]


def sha_file(p):
    return hashlib.sha256(open(os.path.join(C, p), "rb").read()).hexdigest()


def archive(idx, cid, pdir, intake_text, asha):
    t = tasks[idx]
    assert t["clientRequestId"] == cid and t["status"] == "running" and t.get("parent_disposition") is None
    assert t["parent_thread"] == OWN
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
    t["parent_ledger_integration_note"] = ("Intake completed by owner thread " + OWN + " while commits 4d422e71a1 and e2a071e5d3 (thread " + OTHER + ") recorded this entry as running under a different owner; "
                                          "ledger integration applied on top of e2a071e5d3 without altering foreign entries.")


S194_SHA = "a389a0fb63cf48b0e39c0ce8654ac0e10b9b8ac4a8da5882b65e4f121b98411c"
archive(652, "twenty-20261022-fresh-structural-r194-codex-astra-r1", "discovery-structural-r194-parent",
        "discovery-structural-r194-parent/{task-status.json,replay.py,assessment.md,intake.json}; replay all pass (147 selected files/22186011 B, 158-file root with 3 detached carriers and 8 control files, 85 blobs exhausting the five folders of 17/18/18/15/17 blobs against the 13223-entry pinned tree, 74 include edges reparsed from wrapper and preamble bytes with the recorded appendix orders, 80 text blobs fully read and 5 PDFs authenticated only, 52+50 display hashes, 6 recovery rows, byte-exact brief copy, catalogue span CONTENTS.md[540867,544391), 6 completed-r193 copies, 17 history extents fully partitioning i105 and i107 plus the r39 section, navigation 1692 eligible/65 hits with no r160/r161/r162/owner-recovery path, 8 primary PDFs with 90 page rows and 3 renders, policy 160 literals/160 twins/315 wildcards/150 substrings, 3 controls rerun plus 3 parent cases); "
        "parent finite bookkeeping rechecks (middle mapping matrix (2.3), GammaP and GammaF_4 two ways, section 8 inequalities over odd primes to 31, section 6 row/delta-pair bookkeeping, psi-1 invertibility criterion on 120 random matrices over F_5 and F_7); "
        "unpaid: (a) vanishing of the residual counit cone N comparing X with C(x)(P v Q[-5] v Q[-8]) against L_2 of the half-sphere with continuous Z_p action and all coefficient stages; (b) integral spectral realization of the delta generator of the p=3 generic exterior pair (degrees -3,-4) compatible with cooperations, G_F, norm and fracture data; "
        "child-disclosed limits (eight output truncations with recoveries, one wrong-cwd read command that read and wrote nothing, BMR author-site TLS failure not bypassed, speculative HMS v2 URL 404 not cited, Mathew 2017 downloaded unread); brief peer Arithmetic162 archived during the round with all foreign r162/162b/162c activity inside the excluded *arithmetic*r162* namespace; zero count", S194_SHA)

# --- Structural195 dispatch entry (idx655) ---------------------------------------
disp = json.load(open(os.path.join(C, "discovery-structural-r194-parent/structural-r195-dispatch.json")))
assert disp["clientRequestId"] == "twenty-20261022-fresh-structural-r195-codex-astra-r1" and disp["status"] == "running"
assert disp["parent_thread"] == OWN and disp["mcp_command_id"] == "af1e4cc9-2357-48a1-8199-452ec7630192"
assert sha_file("expanded-target-2026-10-17/fresh-structural-r195-brief.txt") == disp["brief_sha256"]
assert os.path.getsize(os.path.join(C, "expanded-target-2026-10-17/fresh-structural-r195-brief.txt")) == disp["brief_bytes"]
for i, t in enumerate(tasks):
    assert t.get("clientRequestId") != disp["clientRequestId"], i
tasks.append(copy.deepcopy(disp))
assert len(tasks) == 656

# --- snapshot -------------------------------------------------------------------
s = T["current_work_snapshot"]
s0 = T0["current_work_snapshot"]
assert set(s["active_task_indices"]) <= {651, 652, 653, 654}, s["active_task_indices"]
s["observed_utc"] = NOW
s["active_task_indices"] = [654, 655]
s["t3_last_polled_running"] = [disp["taskId"]]
s["t3_last_polled_running_note"] = ("Own confirmed list for thread " + OWN + ": Structural195 (idx655) running at dispatch under MCP command af1e4cc9-2357-48a1-8199-452ec7630192. Arithmetic162c (idx654) is owned by thread " + OTHER +
                                    " and cannot be polled from this thread (task_not_found for foreign tasks); its liveness is recorded by its owner only. Structural194 (idx652) is completed and archived by its owner, closing the foreign-owner running record left at 4d422e71a1/e2a071e5d3. "
                                    "The stale active_task_indices [651,652] recorded at e2a071e5d3 (Arithmetic162 archived there, Arithmetic162c dispatched there) is corrected to [654,655].")
s["t3_recorded_running_different_owner"] = [
    {"task_index": 654, "taskId": tasks[654]["taskId"], "parent_thread": OTHER, "shared_record_status": "running",
     "current_thread_status_request": "not_requested_foreign_owner", "current_liveness_verified_here": False,
     "action": "Preserved; no cancellation, duplicate dispatch, requery or live-body/activity inspection. Owner thread archives it."}
]
s["structural194_parent_intake"] = {"disposition": "PREFREEZE_NO_NOMINEE_ARCHIVED", "assessment_sha256": S194_SHA, "intake": "discovery-structural-r194-parent/intake.json", "count_change": 0}
s["structural195_prospective_isolation"] = "discovery-structural-r194-parent/prospective-isolation.json"
pc = s["parent_concurrency_2026_10_22"]
assert set(pc) == {"threads", "rule", "structural193_brief_peer_naming", "structural194_brief_peer_naming"}, set(pc)
pc["threads"] = {OWN: "owner of idx644-647, idx650, idx652 and idx655 (MCP commands b575b956-eb20-481c-b9de-822c8efa824c, then af1e4cc9-2357-48a1-8199-452ec7630192 for the Structural195 dispatch); commits 21adb9f132, 775042d295, 8a57365802, 1d623f6644 and this one",
                 OTHER: "owner of idx648, idx649, idx651, idx653 and idx654 (MCP command eabfe867-92ae-4600-a4b7-dec665823dc7); commits d362a37b73, 143f03e44f, 2789cbceb8, 4d422e71a1, e2a071e5d3"}
pc["structural195_brief_peer_naming"] = ("The Structural195 brief names Arithmetic162c (idx654, Source066) as the sole live peer, which was the live foreign task at dispatch (e2a071e5d3 observed before composition). "
                                         "Arithmetic162c's original brief carries *structural*r195*; the Structural195 supplement line carries *arithmetic*r160* through *arithmetic*r168*, *structural*r195* through *structural*r203* and *analytic*r187* through *analytic*r195*. Mutual prospective guards hold. "
                                         "The Structural195 dispatch ran under a new MCP command id (af1e4cc9-2357-48a1-8199-452ec7630192) of the same owner thread; the task text was pasted from a fresh byte-exact read of the brief file under the authoritative-file header.")
s["note"] = ("Structural194 (idx652, Source318 chromatic splitting filtrations and counterexamples, five manuscripts/85 blobs) completed PREFREEZE/no nominee and archived by its owner thread: the vanishing of the residual counit cone comparing X with the three-term half-sphere decomposition under the continuous Z_p action, and the integral spectral realization of the p=3 generic exterior delta pair, remain unpaid. "
             "Replay all pass and parent finite bookkeeping rechecks; no theorem frozen, no grade, no acceptance/count change. Structural195 (idx655, Source319 counterexamples to the Hahn-Wilson conjecture at height two, one manuscript/12 blobs) dispatched with Astra high/default. "
             "Arithmetic162c (idx654) remains live under thread " + OTHER + " and is not polled here; Arithmetic162/162b archives (idx651/653) preserved untouched. Campaign 19/20, latest R041, one remains; publication STOPPED.")
T["last_parent_progress"] = s["note"]

# --- invariants ---------------------------------------------------------------------
CH = {"observed_utc", "active_task_indices", "t3_last_polled_running", "t3_last_polled_running_note", "t3_recorded_running_different_owner", "note",
      "structural194_parent_intake", "structural195_prospective_isolation", "parent_concurrency_2026_10_22"}
for k in s0:
    if k not in CH:
        assert s[k] == s0[k], k
assert set(s0) - CH <= set(s)
for k in ("rule", "structural193_brief_peer_naming", "structural194_brief_peer_naming"):
    assert pc[k] == s0["parent_concurrency_2026_10_22"][k], k
for i in range(655):
    if i != 652:
        assert tasks[i] == T0["tasks"][i], i
for k in T0:
    if k not in ("tasks", "current_work_snapshot", "last_parent_progress"):
        assert T[k] == T0[k], k
assert T["newAccepted"] == 19 and T["latestAcceptance"] == "R041" and T["remaining"] == 1
open(TS, "w").write(json.dumps(T, indent=2) + "\n")
print(json.dumps({"tasks": len(tasks), "idx655": tasks[655]["clientRequestId"], "idx652": tasks[652]["parent_disposition"], "active": s["active_task_indices"], "utc": NOW}))
