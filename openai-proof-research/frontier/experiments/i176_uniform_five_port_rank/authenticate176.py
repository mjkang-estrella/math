"""Fresh byte-only authentication. No ancestor executable is loaded."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
OWN = Path(__file__).resolve().parent
PARENT = "frontier/experiments/i175_affected_prism_exterior/"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def authenticate(read):
    anchors = {
        "frontier/iterations/i175-affected-prism-exterior.md":
        "7df9e04e808e5f537eef1291b9f323ffd27dfb25c6edd4b76b34d8f23e198ff9",
        PARENT + "seal.json":
        "42636ad1d8a669c8bee23332d7059e0ba957c3467a343ea2b563fdf346905c31",
        PARENT + "verify175.py":
        "e09a4daaa655b9482cb3ac5686fce7e0555eb7d857b8d0ce77b063d184be101a",
    }
    for path, expected in anchors.items():
        assert sha(read(path)) == expected, path
    inv = json.loads(read(PARENT + "inventory.json"))
    seal = json.loads(read(PARENT + "seal.json"))
    pre = json.loads(read(PARENT + "prevalidation.json"))
    assert sha(read(PARENT + "inventory.json")) == seal["inventory_sha256"]
    assert sha(read(PARENT + "prevalidation.json")) == seal["prevalidation_sha256"]
    assert pre["status"] == "PASS" and pre["prevalidation"]
    assert (len(inv["owned"]), len(inv["external"]), len(inv["context"])) == (94, 399, 4)
    for entry in inv["owned"] + inv["external"]:
        data = read(entry["path"])
        assert len(data) == entry["size"] and sha(data) == entry["sha256"], entry["path"]
    for replay in inv["replays"]:
        assert any(x["function"] == replay["function"] and x["byte_identical"]
                   and x["sha256"] == sha(read(replay["payload"]))
                   for x in pre["comparisons"])
    receipt = json.loads(read("frontier/experiments/i175-parent-verification.json"))
    assert receipt["status"] == "PASS"
    assert receipt["replay"]["runtime_seconds"] == 16.19692463602405
    assert len(receipt["replay"]["probes"]) == 8
    assert all(p["blocked"] for p in receipt["replay"]["probes"])
    assert receipt["stderr"] == "empty"
    contexts = [{"path": x["path"], "historical": x["sha256"],
                 "current": sha(read(x["path"])),
                 "drift": sha(read(x["path"])) != x["sha256"]} for x in inv["context"]]
    return {"status": "PASS", "anchors": anchors, "owned": 94, "external": 399,
            "contexts": contexts, "total_external_context": 403,
            "parent_replay_seconds": 16.19692463602405,
            "ancestor_execution": False,
            "replay_limit": "I175 context-current assertion predates ledger integration; "
                            "no ancestor replay or clean-clone reconstruction attempted."}


if __name__ == "__main__":
    result = authenticate(lambda p: (ROOT / p).read_bytes())
    inv = json.loads((ROOT / (PARENT + "inventory.json")).read_bytes())
    listed = {x["path"] for x in inv["owned"]} | set(inv["controls"])
    actual = {"frontier/iterations/i175-affected-prism-exterior.md"}
    for directory in [ROOT / PARENT, ROOT / "frontier/sources/i175_affected_prism_exterior"]:
        actual.update(str(p.relative_to(ROOT)) for p in directory.rglob("*") if p.is_file())
    assert actual == listed, (actual - listed, listed - actual)
    result["complete_owned_membership"] = True
    out = OWN / "authentication.json"
    with out.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps(result, indent=2))
