#!/usr/bin/env python3
"""Parent bookkeeping for the 2026-10-22 explicit resume: dispatch receipts,
prospective-isolation record and tasks.json updates. Run once from the
campaign directory; idempotent on re-run (task entries are keyed by taskId)."""
import hashlib
import json
import os
import sys
from datetime import datetime, timezone

C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(C)
NOW = datetime.now(timezone.utc).isoformat()
PREFIX = "node:delegated-task:command%3Amcp%3Aeb7a5e0a-1bc8-4b0e-9030-d49680777441%3Adelegate-task%3A"
TPREFIX = "thread:delegated-task:command%3Amcp%3Aeb7a5e0a-1bc8-4b0e-9030-d49680777441%3Adelegate-task%3A"
RPREFIX = "run:thread:thread%3Adelegated-task%3Acommand%253Amcp%253Aeb7a5e0a-1bc8-4b0e-9030-d49680777441%253Adelegate-task%253A"
PARENT_THREAD = "164b1204-be68-4540-94bb-0b91055c4381"
PRIOR_PARENT_THREAD = "6742db91-d35c-44d0-a762-e5d9232f5177"


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def ids(cid):
    return {
        "taskId": PREFIX + cid,
        "childThreadId": TPREFIX + cid,
        "childRunId": RPREFIX + cid + ":ordinal:1",
        "childNodeId": PREFIX + cid,
    }


TARGET = {"providerInstanceId": "codex", "model": "gpt-6-astra",
          "options": {"reasoningEffort": "high", "serviceTier": "default"}}
OPTIONS = [{"id": "reasoningEffort", "value": "high"}, {"id": "serviceTier", "value": "default"}]

DISPATCHES = [
    {
        "cid": "twenty-20261022-fresh-arithmetic-r151-codex-astra-r2-user-pause-recovery",
        "label": "Arithmetic151 r2 (user-pause recovery)",
        "output": "fresh-arithmetic-discovery-r151",
        "brief": "user-resume-2026-10-22-parent/arithmetic151-recovery-r2-brief.txt",
        "original_brief": "expanded-target-2026-10-17/fresh-arithmetic-r151-brief.txt",
        "source": 52,
        "receipt": "user-resume-2026-10-22-parent/arithmetic151-r2-dispatch.json",
        "recovers_task_index": 628,
        "round": 2,
    },
    {
        "cid": "twenty-20261022-fresh-arithmetic-r152-codex-astra-r2-user-pause-recovery",
        "label": "Arithmetic152 r2 (user-pause recovery)",
        "output": "fresh-arithmetic-discovery-r152",
        "brief": "user-resume-2026-10-22-parent/arithmetic152-recovery-r2-brief.txt",
        "original_brief": "expanded-target-2026-10-17/fresh-arithmetic-r152-brief.txt",
        "source": 53,
        "receipt": "user-resume-2026-10-22-parent/arithmetic152-r2-dispatch.json",
        "recovers_task_index": 629,
        "round": 2,
    },
    {
        "cid": "twenty-20261022-fresh-structural-r186-codex-astra-r1",
        "label": "Structural186 r1 (Source310 Quillen's conjecture in rational homology)",
        "output": "fresh-structural-discovery-r186",
        "brief": "expanded-target-2026-10-17/fresh-structural-r186-brief.txt",
        "original_brief": None,
        "source": 310,
        "receipt": "discovery-structural-r185-parent/structural-r186-dispatch.json",
        "recovers_task_index": None,
        "round": 1,
    },
]

# ---- dispatch receipts -------------------------------------------------------
for d in DISPATCHES:
    rec = {
        "observed_utc": NOW,
        "label": d["label"],
        "clientRequestId": d["cid"],
        "parent_thread": PARENT_THREAD,
        "target": TARGET,
        "mode": "async",
        "role": "research",
        "brief": d["brief"],
        "brief_sha256": sha(d["brief"]),
        "brief_bytes": os.path.getsize(d["brief"]),
        "task_text": "AUTHORITATIVE BRIEF FILE header (path, sha256, bytes, 'file governs') followed by the complete brief text byte-for-byte",
        "output_root": d["output"],
        "result": dict(ids(d["cid"]), status="running", workState="working",
                       hasPendingChildRuns=False, providerInstanceId="codex",
                       model="gpt-6-astra", options=OPTIONS, hasPendingQuestion=False,
                       pendingApproval=None),
        "status_provenance": "delegate_task return value plus one task_status read at receipt time; no further polling",
        "publication": "STOPPED",
        "parent_count_at_dispatch": 19,
    }
    if d["original_brief"]:
        rec["original_initial_brief"] = {"path": d["original_brief"], "sha256": sha(d["original_brief"])}
        rec["recovers_task_index"] = d["recovers_task_index"]
    json.dump(rec, open(d["receipt"], "w"), indent=1)
    print("wrote", d["receipt"])

# ---- prospective isolation for Structural186 --------------------------------
iso = {
    "observed_utc": NOW,
    "before_structural186_root_and_brief": True,
    "existing_active_peer_original_initial_briefs": [
        {"task_index": 628, "label": "Arithmetic151 (r1 interrupted, r2 recovery re-dispatched with the identical original brief)",
         "brief": "expanded-target-2026-10-17/fresh-arithmetic-r151-brief.txt",
         "sha256": sha("expanded-target-2026-10-17/fresh-arithmetic-r151-brief.txt"),
         "literal_existing_exclusion": "*structural*r186*"},
        {"task_index": 629, "label": "Arithmetic152 (r1 interrupted, r2 recovery re-dispatched with the identical original brief)",
         "brief": "expanded-target-2026-10-17/fresh-arithmetic-r152-brief.txt",
         "sha256": sha("expanded-target-2026-10-17/fresh-arithmetic-r152-brief.txt"),
         "literal_existing_exclusion": "*structural*r186*"},
    ],
    "both_original_initial_guards_cover_entire_structural186_namespace": True,
    "recovery_briefs_contain_original_briefs_byte_for_byte": True,
    "no_live_Arithmetic151_or_Arithmetic152_body_status_activity_or_findings_read": True,
    "completed_inputs_read_by_parent_before_brief": [
        "fresh-structural-discovery-r185/FINAL.md", "fresh-structural-discovery-r185/REPORT.md",
        "fresh-structural-discovery-r185/DERIVATIONS.md", "fresh-structural-discovery-r185/INTERFACES.md",
        "fresh-structural-discovery-r185/COMPARISON.md", "fresh-structural-discovery-r185/private/READING-LIMITS.md",
        "fresh-arithmetic-discovery-r150 (intake prepared 2026-10-21 before pause)"],
    "limits": "Initial prompt chronology, not OS/perfect isolation.",
    "new_root_created_after_initial_guards_and_before_dispatch": True,
    "new_brief": {"path": "expanded-target-2026-10-17/fresh-structural-r186-brief.txt",
                  "sha256": sha("expanded-target-2026-10-17/fresh-structural-r186-brief.txt"),
                  "bytes": os.path.getsize("expanded-target-2026-10-17/fresh-structural-r186-brief.txt")},
    "source310_preparation": {"one_family": True, "catalogue_extent": [532782, 533720],
                              "title_only_navigation_range": [300, 315],
                              "canonical_objects": 16, "canonical_folders": 1,
                              "parent_read_source_proofs": False},
}
json.dump(iso, open("discovery-structural-r185-parent/prospective-isolation.json", "w"), indent=1)
print("wrote discovery-structural-r185-parent/prospective-isolation.json")

# ---- tasks.json --------------------------------------------------------------
T = json.load(open("tasks.json"))
tasks = T["tasks"]
assert tasks[625]["output"] == "fresh-structural-discovery-r185"
assert tasks[627]["output"] == "fresh-arithmetic-discovery-r150"
assert tasks[628]["output"] == "fresh-arithmetic-discovery-r151"
assert tasks[629]["output"] == "fresh-arithmetic-discovery-r152"

tasks[625].update({
    "parent_disposition": "PREFREEZE_NO_NOMINEE_ARCHIVED",
    "parent_full_intake_pending": False,
    "parent_intake": "discovery-structural-r185-parent/intake.json",
    "parent_assessment_sha256": sha("discovery-structural-r185-parent/assessment.md"),
    "parent_intake_utc": NOW,
    "intake_note": "Terminal notification arrived 2026-10-21 during Arithmetic150 intake; full intake deferred by the explicit user pause and completed on explicit user resume 2026-10-22.",
})
tasks[627].update({
    "parent_disposition": "PREFREEZE_NO_NOMINEE_ARCHIVED",
    "parent_full_intake_pending": False,
    "parent_intake": "discovery-arithmetic-r150-parent/intake.json",
    "parent_assessment_sha256": sha("discovery-arithmetic-r150-parent/assessment.md"),
    "intake_note": "Intake prepared 2026-10-21 before the user pause; committed on explicit user resume 2026-10-22.",
})
for idx, cid, r in ((628, DISPATCHES[0]["cid"], DISPATCHES[0]), (629, DISPATCHES[1]["cid"], DISPATCHES[1])):
    tasks[idx].update({
        "parent_disposition": "USER_PAUSED_RECOVERED_R2",
        "recovery_round": 2,
        "recovery_taskId": PREFIX + cid,
        "recovery_brief": r["brief"],
        "recovery_brief_sha256": sha(r["brief"]),
        "resume_receipt": "user-pause-2026-10-21/RESUME.json",
    })

existing = {t.get("taskId") for t in tasks}
new_indices = {}
for d in DISPATCHES:
    tid = PREFIX + d["cid"]
    if tid in existing:
        new_indices[d["cid"]] = next(i for i, t in enumerate(tasks) if t.get("taskId") == tid)
        continue
    entry = {"observed_utc": NOW, "target": TARGET}
    entry.update(ids(d["cid"]))
    entry.update({
        "status": "running", "workState": "working", "hasPendingChildRuns": False,
        "latestTerminalRunId": None, "latestTerminalStatus": None, "latestTerminalSummary": None,
        "latestTerminalResultContextTransferId": None,
        "providerInstanceId": "codex", "model": "gpt-6-astra", "options": OPTIONS,
        "summary": None, "resultContextTransferId": None, "hasPendingQuestion": False,
        "pendingApproval": None, "waitTimedOut": False,
        "role": "research", "output": d["output"], "brief": d["brief"], "brief_sha256": sha(d["brief"]),
        "source_family_navigation": d["source"], "parent_count_at_dispatch": 19,
        "accepted": False, "count_change": 0, "publication": "STOPPED",
        "dispatch_receipt": d["receipt"], "clientRequestId": d["cid"], "round": d["round"],
        "parent_thread": PARENT_THREAD,
    })
    if d["original_brief"]:
        entry["original_initial_brief"] = d["original_brief"]
        entry["original_initial_brief_sha256"] = sha(d["original_brief"])
        entry["recovers_task_index"] = d["recovers_task_index"]
        entry["status_provenance"] = "explicit user resume ('keep progress') after the 2026-10-21 Pause all; identical original brief re-dispatched with a recovery header; no adoption of interrupted partial work"
    else:
        entry["prospective_isolation"] = "discovery-structural-r185-parent/prospective-isolation.json"
    tasks.append(entry)
    new_indices[d["cid"]] = len(tasks) - 1
print("task indices:", new_indices)

for idx, cid in ((628, DISPATCHES[0]["cid"]), (629, DISPATCHES[1]["cid"])):
    tasks[idx]["recovery_task_index"] = new_indices[cid]

snap = T["current_work_snapshot"]
snap["observed_utc"] = NOW
snap["note"] = ("User explicitly resumed ('keep progress') after the 2026-10-21 Pause all. Structural185 full intake completed and Arithmetic150 prepared intake adopted: both PREFREEZE/no nominee, count unchanged. "
                "Arithmetic151 and Arithmetic152 re-dispatched as r2 recoveries with their identical original briefs; distinct Structural186 (Source310, Quillen's conjecture in rational homology) dispatched. "
                "Three Codex/gpt-6-astra research children running. Campaign remains 19/20/latestR041; public actions STOPPED.")
snap["t3_last_polled_running"] = [PREFIX + d["cid"] for d in DISPATCHES]
snap["accepted_count"] = 19
snap["remaining"] = 1
snap["user_resume_requested"] = True
snap["user_resume_utc"] = NOW
snap["user_resume_receipt"] = "user-pause-2026-10-21/RESUME.json"
snap["user_resume_records"] = "user-resume-2026-10-22-parent"
snap["paused_unfinished_task_indices_recovered_as"] = {"628": new_indices[DISPATCHES[0]["cid"]], "629": new_indices[DISPATCHES[1]["cid"]]}
snap["structural185_parent_intake"] = json.load(open("discovery-structural-r185-parent/intake.json"))
snap["arithmetic150_parent_intake"] = json.load(open("discovery-arithmetic-r150-parent/intake.json"))
snap["structural186_prospective_isolation"] = iso
snap["active_task_indices"] = sorted(new_indices.values())

T["last_parent_progress"] = snap["note"]
T["newAccepted"] = 19
T["remaining"] = 1
assert T["latestAcceptance"] == "R041"
json.dump(T, open("tasks.json", "w"), indent=1)
print("tasks.json updated; total tasks", len(tasks))
