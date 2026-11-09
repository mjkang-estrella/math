"""Reconcile publication and problem-link receipts without modifying frozen papers."""
import collections
import datetime
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[2]


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


prepared = read(BASE / "prepared-links.json")
current = read(ROOT / "output/submissions/2026-11-05-remaining/submission-manifest.json")
oct27 = read(ROOT / "output/submissions/2026-10-27-new-discoveries/problem-connections.json")
old_manifest = read(ROOT / "output/submissions/2026-10-25/submission-manifest.json")
old_status = read(ROOT / "frontier/campaigns/2026-10-14/submissions/status.json")
old_posts = read(ROOT / "frontier/campaigns/2026-10-14/submissions/mathdb-solution-posts-2026-10-25.json")

entries = []
for p in current["papers"]:
    assert p.get("solution_url") and p.get("url")
    for url in [p["solution_url"], *p.get("additional_solution_urls", [])]:
        entries.append(dict(batch="2026-11-05-remaining", id=p["id"], title=p["title"],
                            paper_url=p["url"], solution_url=url, scope=p["scope"],
                            status="posted_and_verified_this_session"))

for p in prepared:
    assert p["status"] in {"posted_and_verified", "already_linked_verified"}, p["id"]
    receipt = read(BASE / "receipts" / (p["id"] + ".json"))
    assert any(a["href"].rstrip("/") == p["url"].rstrip("/") for a in receipt["links"])
    assert any(a["id"] == p["solution_url"].split("#")[1] for a in receipt["ids"])
    entries.append(dict(batch=p["batch"], id=p["id"], title=p["title"], paper_url=p["url"],
                        solution_url=p["solution_url"], scope=p.get("scope", p["summary"]),
                        label=p["label"], status=p["status"], verified_at=p["verified_at"]))

for p in oct27["papers"]:
    for c in p["connections"]:
        assert c["verified"]
        entries.append(dict(batch="2026-10-27-new-discoveries", id=f"D{p['number']}",
                            title=p["title"], paper_url=p["paper_url"], solution_url=c["url"],
                            scope=p["scope"], label=c["label"],
                            status="preserved_prior_verified_receipt", verified_at=c["observed_at_utc"]))

for p in old_posts["posts"]:
    if p["key"] == "R039":
        continue  # already reverified above
    assert p["key"] in {"R028", "R030", "R037"}
    receipt = read(BASE / "receipts" / (p["key"] + "-existing.json"))
    v = p["verification"][0]
    paper = next(x for x in v["links"] if "/abs/" in x)
    assert any(a["href"] == paper for a in receipt["links"])
    entries.append(dict(batch="2026-10-25" if p["key"] == "R037" else "2026-10-17",
                        id=p["key"], title=next(a["text"] for a in receipt["links"] if a["href"] == paper),
                        paper_url=paper, solution_url=v["url"], scope=p["summary"],
                        label="partial_progress", status="already_linked_verified"))

reasons = {
    "R025": "Functional fluctuations for the actual deterministic hard-sphere gas on a regular Boltzmann lifespan; nearby records concern annihilated dynamics, equilibrium repulsion, or spectral gaps. No exact fluctuation question was established.",
    "R026": "An integral regular summand in a staircase tensor CUBE over every ring; the available Saxl records concern tensor SQUARES. The cube theorem does not settle the square claim.",
    "R029": "The specific complex-projective-plane set has Borsuk number nine in ambient dimension eight. It is not a counterexample to the d+1 bound, nor a solution of the general Borsuk problem.",
    "R031": "Transitive Boolean-function sensitivity separation; no exact matching transitive-sensitivity problem was established by the corpus search.",
    "R032": "Continuum Coulomb-energy QMA verification; nearby Coulomb records concern binding, stability, or other analytic questions, not this computational promise problem.",
    "R033": "Fourth-moment comparison and conditional fluctuation transfer for zero-field SK; this does not establish the critical-temperature variance conjectures found in the corpus.",
    "R034": "Advanced Mukai classification under specified stronger quantum-correspondence inputs; no exact advanced-classification record was established. The broader Mukai inequality is a source premise.",
    "R035": "Reverse-complement superstring approximation from stipulated ordinary contracts; no exact reverse-complement question was established. Ordinary shortest-superstring problems have different scope.",
    "R038": "Negative-type metrics and trace-class average distortion; the negative-type graph records found in the corpus do not express this embedding question.",
    "R040": "A conditional two-variable microstates/nonmicrostates free-entropy gap; no exact matching identity record was established. The mutual-free-information identity found in the corpus is different.",
    "R041": "A projection-body volume UPPER bound for four-polytopes with at most six facets; the Petty minimization, polar fixed-point and second-projection-body records are different problems. No exact matching upper-bound record was established.",
}
unmapped = []
for id, reason in reasons.items():
    if id in old_status:
        paper_url = old_status[id]["mathdb_url"]
    else:
        raise AssertionError(id)
    if int(id[1:]) >= 31:
        title = next(p["title"] for p in old_manifest["papers"] if p["finding"] == id)
    else:
        title = {"R025": "Functional hard-sphere fluctuations on a regular Boltzmann lifespan",
                 "R026": "An integral regular summand in every staircase Specht tensor cube",
                 "R029": "The Borsuk number of the complex projective plane is nine"}[id]
    unmapped.append(dict(id=id, title=title, paper_url=paper_url, status="no_defensible_mapping_established", reason=reason))

linked_papers = {e["paper_url"] for e in entries}
assert len(entries) == 103, len(entries)
assert len(linked_papers) == 99, len(linked_papers)
assert len(unmapped) == 11
assert not linked_papers.intersection(x["paper_url"] for x in unmapped)
assert len({(e["paper_url"], e["solution_url"].split("/p/")[1].split("/")[0].split("#")[0]) for e in entries}) == len(entries)
assert sum(p["status"] == "posted_and_verified" for p in prepared) == 55

summary = dict(
    completed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    status="all_defensible_mappings_posted_or_preserved",
    inventory_scope="110 publicly submitted papers found in repository publication receipts: R023–R041, D1–D30, November 2 (22), November 4 (28), and current batch (11). R001–R022 had no public submission receipt in this audit and are not counted.",
    current_papers_submitted=11, current_new_solution_links=12,
    earlier_new_solution_links=55, existing_links_preserved=36,
    linked_unique_papers=99, total_problem_solution_links=103,
    papers_without_defensible_mapping=11, entries=entries, unresolved_mappings=unmapped,
    verification_scope="Every new entry and the four oldest historical entries were observed publicly in this session. The 32 October 27 links retain their prior verified receipts; they were not all re-fetched. This work is publication/link maintenance, not a fresh proof review or Lean replay.",
    new_problem_records=[{"id": p["id"], "problem_url": p["problem_url"]} for p in prepared if "problem_url" in p],
)
write(BASE / "completion-manifest.json", summary)

lines = ["# MathDB publication and problem–solution link audit", "",
         "11 papers submitted in the current batch, with 12 problem–solution entries (including the duplicate NIM question).",
         "55 missing links added for earlier papers. 36 previously posted links preserved. Across the 110-paper publication inventory, 99 distinct papers now have 103 recorded links; 11 papers remain without a defensible problem mapping.", "",
         summary["verification_scope"], "",
         "Entries retain proof, counterexample, or partial-progress scope. The oldest conditional results explicitly state their stipulated source inputs and limited Lean coverage. A posted solution is not MathDB endorsement or acceptance. No new discovery credit is claimed.", "",
         "Seven source-exact problem records were added after bounded cached-corpus and live-site searches: D32, D33, D35, D36, D37, D39 and R027. Adjacent source conjectures were not substituted. Search incompleteness is not a claim that no other record exists.", "",
         "## Linked papers", "", "| Batch | Paper | Problem–solution entry | Status |", "|---|---|---|---|"]
for e in entries:
    pid = e["solution_url"].split("/p/")[1].split("/")[0].split("#")[0]
    lines.append(f"| {e['batch']} | [{e['id']}: {e['title'].replace('|', ' / ')}]({e['paper_url']}) | [{pid}]({e['solution_url']}) | {e['status']} |")
lines += ["", "## Unresolved mappings", "",
          "These papers remain public. No unrelated problem or broader conjecture was marked solved to force a connection.", "",
          "| Paper | Reason no link was added |", "|---|---|"]
for p in unmapped:
    lines.append(f"| [{p['id']}: {p['title']}]({p['paper_url']}) | {p['reason']} |")
lines += ["", "## Connection and upload resolution", "",
          "T3 browser access succeeded. A temporary Cloudflare 1015 response and an application posting-rate limit cleared after cooldown; no identity or network bypass was used. The large 333709 package exceeded transfer and per-file limits, so it was losslessly repackaged as three JSON chunks plus an extractor. Extraction reproduced all 848 original filenames and bytes. An expired authentication token during upload was resolved by resuming the pending submission, retaining verified attachments.", "",
          "See [connection diagnostics](connection-diagnostics.json), [completion manifest](completion-manifest.json), [prepared and posted entry texts](prepared-links.json), and [current submission index](../2026-11-05-remaining/SUBMISSION-INDEX.md).", ""]
(BASE / "PROBLEM-CONNECTION-INDEX.md").write_text("\n".join(lines))

diagnostics = read(BASE / "connection-diagnostics.json")
diagnostics["current_post_limit"]["resolved"] = True
diagnostics["current_post_limit"]["resolution"] = "Cooldown, then the retained modal was submitted successfully. Subsequent posts used pacing and were publicly verified."
diagnostics["final_state"] = "Connected; authorized uploads and defensible link backfills completed. Remaining mapping gaps are mathematical scope gaps, not connection failures."
write(BASE / "connection-diagnostics.json", diagnostics)
print(json.dumps({k: v for k, v in summary.items() if k not in {"entries", "unresolved_mappings", "new_problem_records"}}, indent=2))
