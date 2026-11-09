"""One-launch guard and an external 60-second wall deadline. Never retries."""
import datetime
import json
import os
from pathlib import Path
import subprocess
import sys
import time


def main():
    root = Path(__file__).resolve().parent
    # The wall cap begins before guard/config/source loading and process startup.
    start = time.monotonic()
    deadline = start + 60.0
    with (root / "RUN-ONCE.json").open("x") as f:
        json.dump({"started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   "start_monotonic": start, "deadline_monotonic": deadline,
                   "seconds_cap": 60, "launches": 1}, f, indent=2)
        f.write("\n")
    outcome = {"launches": 1, "hard_timeout": False}
    with (root / "stdout.txt").open("x") as out, (root / "stderr.txt").open("x") as err:
        env = dict(os.environ)
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        proc = subprocess.Popen([sys.executable, "-B", str(root / "assay.py"),
                                 repr(start), repr(deadline)], cwd=root, env=env,
                                 stdout=out, stderr=err)
        try:
            returncode = proc.wait(timeout=max(0.001, deadline - time.monotonic()))
        except subprocess.TimeoutExpired:
            outcome["hard_timeout"] = True
            proc.kill()
            returncode = proc.wait()
    outcome["returncode"] = returncode
    outcome["wall_seconds_through_process_exit"] = time.monotonic() - start
    outcome["within_wall_cap"] = outcome["wall_seconds_through_process_exit"] <= 60
    # Recovery is retention only: no arithmetic candidate/reference is restarted.
    if not (root / "results.json").exists():
        config = json.loads((root / "cases.json").read_text())
        records = [{**case, "status": "unstarted"} for case in config["cases"]]
        completed = root / "records.jsonl"
        if completed.exists():
            for line in completed.read_text().splitlines():
                row = json.loads(line)
                records[row["index"]] = row
        progress = root / "progress.json"
        if progress.exists():
            row = json.loads(progress.read_text())
            if records[row["index"]]["status"] != "completed":
                row["status"] = "stopped"
                row["stop_reason"] = "hard_timeout_or_process_error"
                records[row["index"]] = row
        recovered = {"status": "hard_timeout_or_process_error", "records": records,
            "unstarted_indices": [r["index"] for r in records if r["status"] == "unstarted"],
            "accounting": "incomplete; retain events.jsonl, never substitute zero",
            "verified_complete_improvement": "NONE"}
        (root / "results-recovered.json").write_text(json.dumps(recovered, indent=2) + "\n")
    (root / "execution.json").write_text(json.dumps(outcome, indent=2) + "\n")
    print(json.dumps(outcome, sort_keys=True))
    return 0 if returncode == 0 and outcome["within_wall_cap"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
