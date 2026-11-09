"""Build a JSON-serializable snapshot of research status from live files and git.

Extraction is deliberately literal: titles, Status lines and STATE sections are
copied verbatim. The only derived labels are keyword "hints" on a finding's own
Status text, and each hint carries the exact phrase that triggered it so a
reader can see why it was applied. Ambiguous or missing data stays visible as
"unclassified" / warnings rather than being upgraded.
"""

from __future__ import annotations

import json
import math
import os
import re
import time
from datetime import datetime, timezone

from . import gitinfo, live, sources

# Accept naming variations (w21_x.md, W0021-x.md) and normalize IDs to W###.
FINDING_FILE_RE = re.compile(r"[Ww]0*(\d{1,4})[-_][A-Za-z0-9._-]+\.(md|json|txt)")
PROPOSAL_FILE_RE = re.compile(r"[Ww]0*(\d{1,4})[-_][A-Za-z0-9._-]+\.md")

# Ordered (category, label, regex) keyword rules applied to a finding's Status text.
# Ordered (category, label, regex, negatable) keyword rules applied to a finding's
# title + Status text. Positive rules are skipped when the match is negated in
# the same clause ("not an accepted ... experimental finding").
HINT_RULES: list[tuple[str, str, re.Pattern[str], bool]] = [
    ("rejected", "not accepted / rejected", re.compile(r"not accepted|\brejected\b", re.I), False),
    ("pending", "unaccepted / pending / partly not approved", re.compile(r"unaccepted|pending|in progress|requires further|not yet|not approved", re.I), False),
    ("negative", "negative result", re.compile(r"negative (result|example)s?|counterexamples?", re.I), True),
    ("reviewed", "independently reviewed / verified", re.compile(r"independently (reviewed|verified|accepted)|review passed|\bverified\b|\bPASS\b", re.I), True),
    ("proved", "formal (Lean) result", re.compile(r"kernel-checked|formal result|\bproved\b|generic [\w-]+ facts|modular arithmetic|arithmetic(/| support| result)|correctness|component result|abstract runner", re.I), True),
    ("experiment", "finite experiment / check", re.compile(r"experiment|finite[- ]check", re.I), True),
    ("design", "design / contract / policy", re.compile(r"\bdesign\b|contract|policy|proposal|implementation", re.I), True),
    ("no-speedup", "explicitly no speedup claimed", re.compile(r"no (speedup|speed|new speed|improved|faster|total-work|accepted calibrated|solver)|not an ecdlp improvement", re.I), False),
]
_NEGATION_RE = re.compile(r"\b(not|no|nor|never|without)\b[^.;:]*$", re.I)

OPEN_SENTENCE_RE = re.compile(
    r"(remain(s)? (open|unproved|unpriced)|unproved|not established|no (faster|speedup)|blocked|open prerequisites|is open|NOT APPROVED|requires independent)",
    re.I,
)


def _iso(ts: float | None) -> str | None:
    if ts is None:
        return None
    return datetime.fromtimestamp(ts, timezone.utc).isoformat(timespec="seconds")


def _ws(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def split_sections(text: str) -> list[dict]:
    """Split Markdown into heading sections, ignoring headings inside code fences."""
    sections: list[dict] = [{"level": 0, "title": "", "body": []}]
    in_fence = False
    for line in text.splitlines():
        if line.lstrip().startswith("```"):
            in_fence = not in_fence
        m = None if in_fence else re.match(r"^(#{1,6})\s+(.*?)\s*#*\s*$", line)
        if m:
            sections.append({"level": len(m.group(1)), "title": m.group(2), "body": []})
        else:
            sections[-1]["body"].append(line)
    return [{"level": s["level"], "title": s["title"], "body": "\n".join(s["body"]).strip()} for s in sections]


def paragraphs(text: str) -> list[str]:
    return [p.strip() for p in re.split(r"\n\s*\n", text) if p.strip()]


def bullets(text: str) -> list[str]:
    items: list[str] = []
    for line in text.splitlines():
        m = re.match(r"^\s*[-*]\s+(.*)$", line)
        if m:
            items.append(m.group(1).strip())
        elif items and line.startswith("  ") and line.strip():
            items[-1] += " " + line.strip()
    return items


def sentences(text: str) -> list[str]:
    flat = _ws(text)
    return [s.strip() for s in re.split(r"(?<=[.;])\s+(?=[A-Z`])", flat) if s.strip()]


def classify_status(status: str) -> list[dict]:
    hints = []
    text = status or ""
    for category, label, pat, negatable in HINT_RULES:
        for m in pat.finditer(text):
            if negatable and _NEGATION_RE.search(text[max(0, m.start() - 60):m.start()]):
                continue
            hints.append({"category": category, "label": label, "matched": m.group(0)})
            break
    return hints


def parse_finding_md(rel: str, text: str) -> dict:
    secs = split_sections(text)
    title_sec = next((s for s in secs if s["level"] == 1), None)
    title = title_sec["title"] if title_sec else os.path.basename(rel)
    intro = title_sec["body"] if title_sec else (secs[0]["body"] if secs else "")
    first_para = paragraphs(intro)[0] if paragraphs(intro) else ""
    status, status_from = "", None
    m = None
    for para in paragraphs(intro)[:3]:
        m = re.search(r"\b(Status|Verdict)\**\s*:\**\s*(.*?)(?:\n\s*\n|$)", para + "\n\n", re.S | re.I)
        if m:
            break
    if m:
        status, status_from = _ws(m.group(2)), "Status line" if m.group(1).lower() == "status" else "Verdict line"
    elif first_para:
        status, status_from = _ws(first_para), "first paragraph (no Status line)"
    date_m = re.search(r"Date:\s*(\d{4}-\d{2}-\d{2})", intro)
    hyp = ""
    for s in secs:
        if re.search(r"hypothes|question|claim|purpose|motivation", s["title"], re.I):
            ps = paragraphs(s["body"])
            if ps:
                hyp = _ws(ps[0])[:700]
                break
    return {
        "title": title,
        "date": date_m.group(1) if date_m else None,
        "status": status[:1200],
        "status_from": status_from,
        "hints": classify_status(f"{title}. {status}"),
        "headings": [s["title"] for s in secs if s["level"] >= 2][:40],
        "hypothesis": hyp,
    }


def summarize_results(rel: str, text: str) -> dict:
    """Summarize a machine-readable results file without inventing semantics."""
    out: dict = {"path": rel}
    if rel.endswith(".json"):
        try:
            data = json.loads(text)
        except ValueError as exc:
            return {**out, "error": f"malformed JSON: {exc.msg} at line {exc.lineno}"}
        if isinstance(data, dict):
            out["fields"] = {
                k: v for k, v in data.items()
                if isinstance(v, (str, int, float, bool)) or (isinstance(v, list) and len(v) <= 4 and all(isinstance(x, (int, float, str)) for x in v))
            }
            rows = data.get("rows")
            if isinstance(rows, list) and rows and all(isinstance(r, dict) for r in rows):
                table = _bsgs_table(rows)
                if table:
                    out["table"] = table
        return out
    lines = [ln for ln in text.splitlines() if ln.strip()]
    out["lines"] = lines[:40]
    return out


def _bsgs_table(rows: list[dict]) -> dict | None:
    variants = ["exhaustive", "linear_bsgs", "ordered_bsgs"]
    if not all(isinstance(r.get("curve"), dict) and all(isinstance(r.get(v), dict) for v in variants) for r in rows):
        return None
    body = []
    for r in rows:
        row = {"q": r["curve"].get("q"), "secrets_tested": r.get("secrets_tested")}
        for v in variants:
            row[f"{v}.adds"] = r[v].get("adds")
            row[f"{v}.max_sort_plus_lookup"] = r[v].get("max_sort_plus_lookup")
        body.append(row)
    return {"kind": "bsgs-variants", "columns": list(body[0].keys()), "rows": body}


def parse_state(text: str) -> dict:
    secs = split_sections(text)
    title_sec = next((s for s in secs if s["level"] == 1), None)
    intro = title_sec["body"] if title_sec else ""
    first = paragraphs(intro)[0] if paragraphs(intro) else ""
    status_m = re.search(r"Status\**\s*:\**\s*(.*?)(?:\(\d{4}-\d{2}-\d{2}\)|\.\s|$)", _ws(first))
    level2 = [s for s in secs if s["level"] == 2]

    def section(pattern: str) -> str:
        sec = next((s for s in level2 if re.search(pattern, s["title"], re.I)), None)
        return sec["body"] if sec else ""
    claimed = re.findall(r"(\d+) named theorem (?:dependency )?audits", text)
    open_sentences = [s for s in sentences(text) if OPEN_SENTENCE_RE.search(s)]
    return {
        "phase": _ws(status_m.group(1)) if status_m else None,
        "status_paragraph": _ws(first),
        "headline_sentences": [s for s in sentences(first) if OPEN_SENTENCE_RE.search(s) or re.search(r"discovered|established", s)],
        "sections": [{"title": s["title"], "body": s["body"]} for s in secs if s["level"] == 2],
        "established_milestones": bullets(section(r"milestone|achievement")),
        "current_live_work": bullets(section(r"live work|active work|current work|in progress")),
        "next_step": section(r"^next"),
        "open_sentences": open_sentences[:40],
        "claimed_audit_count": int(claimed[0]) if claimed else None,
    }


def parse_audit(text: str) -> dict:
    names = re.findall(r"^#print axioms\s+(\S+)", text, re.M)
    modules: dict[str, int] = {}
    for n in names:
        parts = n.split(".")
        mod = parts[1] if len(parts) > 2 and parts[0] == "Research" else "Research (root)"
        modules[mod] = modules.get(mod, 0) + 1
    return {"count": len(names), "names": names, "modules": modules}


def parse_order(text: str, symbol: str = "n") -> int | None:
    m = re.search(rf"^def {re.escape(symbol)}\s*:\s*Nat\s*:=\s*(0x[0-9A-Fa-f]+|\d+)\s*$", text, re.M)
    if not m:
        return None
    return int(m.group(1), 0)


def complexity(manifest: dict, order: int | None) -> dict:
    log2_n = math.log2(order) if order else None
    rows = []
    for ref in manifest.get("classical_references", []):
        spec = ref.get("log2_from_order")
        log2_ops = None
        if spec and log2_n is not None:
            coef = float(spec.get("coefficient", 1.0))
            base = log2_n if spec.get("kind") == "linear" else log2_n / 2
            log2_ops = base + math.log2(coef)
        rows.append({**ref, "log2_ops": log2_ops})
    return {
        "order_hex": hex(order) if order else None,
        "order_log2": log2_n,
        "order_bits": order.bit_length() if order else None,
        "references": rows,
        "rounded_reference_log2": manifest.get("rounded_reference_log2"),
        "rounded_reference_note": manifest.get("rounded_reference_note"),
    }


def verify_manifest_results(manifest: dict, research_root: str, audit_names: set[str], finding_ids: set[str]) -> list[dict]:
    cache: dict[str, str | None] = {}
    out = []
    for item in manifest.get("repo_results", []):
        ev = item.get("evidence", {}) or {}
        src = ev.get("source")
        if src not in cache:
            f = sources.try_read(research_root, src) if src else None
            cache[src] = _ws(f.text) if f else None
        text = cache[src]
        quote = ev.get("quote", "")
        checks = {
            "source_present": text is not None,
            "quote_found": bool(text and quote and _ws(quote) in text),
            "theorems_missing": [t for t in ev.get("theorems", []) if t not in audit_names],
            "findings_missing": [w for w in ev.get("findings", []) if w not in finding_ids],
        }
        checks["ok"] = checks["source_present"] and checks["quote_found"] and not checks["theorems_missing"] and not checks["findings_missing"]
        out.append({**item, "verification": checks})
    return out


def load_manifest(path: str) -> tuple[dict, str | None]:
    try:
        with open(path, encoding="utf-8") as fh:
            data = json.load(fh)
        if not isinstance(data, dict):
            return {}, "manifest is not a JSON object"
        return data, None
    except (OSError, ValueError) as exc:
        return {}, f"manifest unreadable: {exc}"


def build_snapshot(research_root: str, repo_root: str, manifest_path: str, research_pathspec: str | None = None) -> dict:
    warnings: list[str] = []
    started = time.time()
    files = sources.list_sources(research_root)
    stats = {}
    for rel in files:
        st = sources.stat_source(research_root, rel)
        if st:
            stats[rel] = {"path": rel, "size": st.st_size, "mtime": _iso(st.st_mtime), "mtime_epoch": st.st_mtime}
    if not os.path.isdir(research_root):
        warnings.append(f"research directory missing: {research_root}")

    # Git.
    head = gitinfo.head(repo_root)
    commits, log_err = gitinfo.log(repo_root, 200)
    status_entries, status_err = gitinfo.status(repo_root, research_pathspec)
    for err, what in ((head.get("error"), "git rev-parse"), (log_err, "git log"), (status_err, "git status")):
        if err:
            warnings.append(f"{what} failed: {err}")
    prefix = (research_pathspec.rstrip("/") + "/") if research_pathspec else ""
    dirty = {}
    for e in status_entries:
        rel = e["path"][len(prefix):] if prefix and e["path"].startswith(prefix) else e["path"]
        dirty[rel] = e["state"]

    # STATE.md
    state_file = sources.try_read(research_root, "research/STATE.md")
    if state_file:
        state = parse_state(state_file.text)
        state["path"] = "research/STATE.md"
        state["mtime"] = _iso(state_file.mtime)
    else:
        state = None
        warnings.append("research/STATE.md missing or unreadable")

    # Audit.lean
    audit_file = sources.try_read(research_root, "Audit.lean")
    audit = parse_audit(audit_file.text) if audit_file else {"count": None, "names": [], "modules": {}}
    if not audit_file:
        warnings.append("Audit.lean missing or unreadable")

    # Findings.
    commits_by_id: dict[str, list[str]] = {}
    for c in reversed(commits):
        for wid in c.finding_ids:
            commits_by_id.setdefault(wid, []).append(c.short)
    findings: dict[str, dict] = {}
    results: list[dict] = []
    for rel in files:
        if not rel.startswith("research/findings/"):
            continue
        name = rel.rsplit("/", 1)[-1]
        m = FINDING_FILE_RE.fullmatch(name)
        wid = live.norm_wid(m.group(1)) if m else "unnumbered"
        entry = findings.setdefault(wid, {"id": wid, "files": [], "title": None, "status": "", "hints": [], "date": None})
        entry["files"].append({**stats.get(rel, {"path": rel}), "git": dirty.get(rel, "committed")})
        f = sources.try_read(research_root, rel)
        if f is None:
            warnings.append(f"{rel}: unreadable (possibly being written)")
            continue
        if name.endswith(".md") and entry["title"] is None:
            try:
                entry.update(parse_finding_md(rel, f.text))
                entry["primary"] = rel
            except Exception as exc:  # malformed source must not break the snapshot
                warnings.append(f"{rel}: parse error {type(exc).__name__}")
        elif not name.endswith(".md"):
            summary = summarize_results(rel, f.text)
            summary["finding_id"] = wid
            if "error" in summary:
                warnings.append(f"{rel}: {summary['error']}")
            results.append(summary)
    for wid, entry in findings.items():
        entry["commits"] = commits_by_id.get(wid, [])
        entry["uncommitted"] = any(fi.get("git") != "committed" for fi in entry["files"])
        entry["latest_mtime"] = max((fi.get("mtime_epoch", 0) for fi in entry["files"]), default=0)
        if entry["title"] is None:
            entry["title"] = f"{wid} (no finding Markdown record yet)"
            for rel in files:
                pm = PROPOSAL_FILE_RE.fullmatch(rel.rsplit("/", 1)[-1])
                if rel.startswith("research/proposals/") and pm and live.norm_wid(pm.group(1)) == wid:
                    pf = sources.try_read(research_root, rel)
                    if pf:
                        parsed = parse_finding_md(rel, pf.text)
                        entry.update(title=parsed["title"], status=parsed["status"], hints=parsed["hints"],
                                     status_from=f"proposal {rel} (no finding record yet)", primary=rel)
                    break
        if not entry["hints"]:
            entry["hints"] = [{"category": "unclassified", "label": "unclassified (no keyword match)", "matched": ""}]

    proposals = []
    for rel in files:
        if rel.startswith("research/proposals/"):
            f = sources.try_read(research_root, rel)
            parsed = parse_finding_md(rel, f.text) if f else {"title": rel, "status": ""}
            proposals.append({**stats.get(rel, {"path": rel}), "title": parsed["title"], "status": parsed["status"],
                              "archived": "/archive/" in rel, "git": dirty.get(rel, "committed")})

    lean_modules = []
    for rel in files:
        if rel.startswith("Research/") and rel.endswith(".lean"):
            mod = rel[len("Research/"):-len(".lean")]
            lean_modules.append({**stats.get(rel, {"path": rel}), "module": mod,
                                 "audits": audit["modules"].get(mod, 0), "git": dirty.get(rel, "committed")})

    # Complexity / manifest.
    manifest, merr = load_manifest(manifest_path)
    if merr:
        warnings.append(merr)
    order_rel = (manifest.get("problem") or {}).get("order_source", "Research/Secp256k1.lean")
    order_file = sources.try_read(research_root, order_rel)
    order = parse_order(order_file.text, (manifest.get("problem") or {}).get("order_symbol", "n")) if order_file else None
    if order is None:
        warnings.append(f"group order not parsed from {order_rel}")
    finding_ids = set(findings)
    repo_results = verify_manifest_results(manifest, research_root, set(audit["names"]), finding_ids)
    reviewed_through = manifest.get("reviewed_findings_through")
    newer = sorted(w for w in finding_ids if reviewed_through and w.startswith("W") and w > reviewed_through)

    findings_list = sorted(findings.values(), key=lambda e: e["id"])
    commits_json = [c.to_json() for c in commits]
    manifest_ok_findings = {w for r in repo_results if r["verification"]["ok"] for w in (r.get("evidence") or {}).get("findings", [])}
    try:
        live_outcome = live.outcome(state_file.text if state_file else None, (state or {}).get("sections"),
                                    (state or {}).get("status_paragraph"), (state or {}).get("mtime"), findings_list)
    except Exception as exc:  # never let a heuristic failure hide the rest of the snapshot
        warnings.append(f"outcome extraction failed: {type(exc).__name__}")
        live_outcome = {"status": "unknown", "label": live.LABELS["unknown"][0], "explanation": "extraction error", "headline": [], "elsewhere": [], "finding_signals": [], "primary": None}
    try:
        live_feed = live.achievements(state, findings_list, commits_json, manifest_ok_findings, reviewed_through)
    except Exception as exc:
        warnings.append(f"achievement feed extraction failed: {type(exc).__name__}")
        live_feed = {"reported": [], "findings": []}

    latest_file = max(stats.values(), key=lambda s: s["mtime_epoch"], default=None)
    latest_commit = commits[0].to_json() if commits else None
    commit_epoch = None
    if latest_commit:
        try:
            commit_epoch = datetime.fromisoformat(latest_commit["commit_date"]).timestamp()
        except ValueError:
            pass
    file_epoch = latest_file["mtime_epoch"] if latest_file else None
    latest_change = max([t for t in (commit_epoch, file_epoch) if t is not None], default=None)

    return {
        "generated_at": _iso(time.time()),
        "build_ms": round((time.time() - started) * 1000),
        "repo": {
            "head": head,
            "latest_commit": latest_commit,
            "latest_file_change": {"path": latest_file["path"], "mtime": latest_file["mtime"]} if latest_file else None,
            "latest_repo_change": _iso(latest_change),
            "working_tree": [{"path": k, "state": v} for k, v in sorted(dirty.items())],
            "commit_count": len(commits),
        },
        "state": state,
        "audit": {"count": audit["count"], "claimed_in_state": state.get("claimed_audit_count") if state else None,
                  "modules": audit["modules"]},
        "findings": findings_list,
        "outcome": live_outcome,
        "achievements": live_feed,
        "results": results,
        "proposals": proposals,
        "lean_modules": lean_modules,
        "commits": commits_json,
        "complexity": complexity(manifest, order),
        "repo_results": repo_results,
        "manifest": {
            "about": manifest.get("about"),
            "reviewed_at_commit": manifest.get("reviewed_at_commit"),
            "reviewed_on": manifest.get("reviewed_on"),
            "reviewed_findings_through": reviewed_through,
            "findings_newer_than_manifest": newer,
            "problem": manifest.get("problem"),
        },
        "estimator": manifest.get("estimator", {}),
        "sources": sorted(stats.values(), key=lambda s: s["path"]),
        "warnings": warnings,
    }
