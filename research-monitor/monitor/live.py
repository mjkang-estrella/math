"""Live, source-attributed overview: headline outcome and latest reported achievements.

Nothing here is hardcoded research status. Every value is recomputed from the
current STATE.md / findings / git log on each snapshot, and every item carries
the literal source sentence it came from. The outcome polarity is a keyword
heuristic that is displayed together with the sentence it read; it can only
ever say "reported by STATE.md", never "verified".
"""

from __future__ import annotations

import re
from datetime import datetime

# Sentences about an end-to-end speedup / break of the target problem.
OUTCOME_TOPIC_RE = re.compile(
    r"\b(faster\b|speed-?ups?\b|speed up\b|cryptographic(?:ally)? break|break(?:s|ing)? (?:secp256k1|ecdlp|the)|"
    r"sub-?exponential|improved (?:ecdlp |generic )?(?:algorithm|exponent|complexity)|beats? (?:rho|pollard|bsgs)|"
    r"below (?:the )?(?:rho|2\^128|generic)|verified improvements?\b)",
    re.I,
)
# A negation shortly before the topic word, in the same clause ("No faster ...", "not a speedup").
_NEG_BEFORE_RE = re.compile(r"\b(no|not|never|nor|none|without|neither|cannot|isn't|wasn't|hasn't|haven't)\b[^.;:]{0,80}$", re.I)
# A trailing qualifier that keeps the claim unestablished ("... remains open").
_NEG_AFTER_RE = re.compile(
    r"^[^.;]{0,120}\b(remains? (?:open|unproved|unknown|unestablished)|(?:is|are|was|were|has|have) not (?:yet )?(?:been )?"
    r"(?:established|discovered|shown|proved|demonstrated|found)|is open|unproved|not established)\b",
    re.I,
)

HASH_RE = re.compile(r"`([0-9a-f]{7,40})`")
WID_RE = re.compile(r"\b[Ww]0*(\d{1,4})\b")
CHECKPOINT_VERB_RE = re.compile(r"\b(committed|integrated|milestones?|verified|accepted|passed|PASS|established|proved)\b", re.I)


def norm_wid(num: str | int) -> str:
    return "W%03d" % int(num)


def wids_in(text: str) -> list[str]:
    seen: list[str] = []
    for m in WID_RE.finditer(text or ""):
        w = norm_wid(m.group(1))
        if w not in seen:
            seen.append(w)
    return seen


# Report-style label with an empty value ("Verified improvement versus baseline: NONE.").
_NONE_VALUE_RE = re.compile(r"^[^.;:]{0,80}:\s*[*_`]*\s*(?:none|no|nil|zero)\b", re.I)


def sentence_polarity(sentence: str) -> str | None:
    """Return "negative", "positive" or None (sentence does not discuss the outcome)."""
    m = OUTCOME_TOPIC_RE.search(sentence)
    if not m:
        return None
    after = sentence[m.end():]
    if _NEG_BEFORE_RE.search(sentence[: m.start()]) or _NEG_AFTER_RE.search(after) or _NONE_VALUE_RE.search(after):
        return "negative"
    return "positive"


def _split_sentences(text: str) -> list[str]:
    flat = re.sub(r"\s+", " ", text or "").strip()
    return [s.strip() for s in re.split(r"(?<=[.;!?])\s+(?=[A-Z`*(])", flat) if s.strip()]


LABELS = {
    "reported_none": ("None reported", "STATE.md explicitly reports no end-to-end speedup or break."),
    "reported_positive": ("Claim reported — evidence review required",
                          "STATE.md contains a sentence that reads as a positive speedup/break claim. The monitor has not reviewed it."),
    "conflicting": ("Conflicting — not assessed", "Live sources contain both negative and possibly positive statements."),
    "unknown": ("Unknown — not assessed", "No explicit statement about an end-to-end speedup was found in the live sources."),
}


def outcome(state_text: str | None, state_sections: list[dict] | None, status_paragraph: str | None,
            state_mtime: str | None, findings: list[dict]) -> dict:
    """Derive the attributed headline outcome from the current STATE.md (and finding statuses)."""
    out: dict = {"source": "research/STATE.md", "source_mtime": state_mtime, "headline": [], "elsewhere": [], "finding_signals": []}
    if state_text is None:
        status = "unknown"
        out["reason"] = "research/STATE.md is missing or unreadable."
    else:
        for s in _split_sentences(status_paragraph or ""):
            p = sentence_polarity(s)
            if p:
                out["headline"].append({"text": s, "polarity": p, "section": "status paragraph"})
        head_texts = {h["text"] for h in out["headline"]}
        for sec in state_sections or []:
            for s in _split_sentences(sec.get("body", "")):
                p = sentence_polarity(s)
                if p and s not in head_texts:
                    out["elsewhere"].append({"text": s, "polarity": p, "section": sec.get("title", "")})
        pols = {h["polarity"] for h in out["headline"]}
        other_pos = any(e["polarity"] == "positive" for e in out["elsewhere"])
        if "positive" in pols and "negative" in pols:
            status = "conflicting"
        elif "positive" in pols:
            status = "reported_positive"
        elif "negative" in pols:
            status = "conflicting" if other_pos else "reported_none"
        else:
            # No headline statement: fall back to the rest of the document, but say so.
            epols = {e["polarity"] for e in out["elsewhere"]}
            if epols == {"negative"}:
                status = "reported_none"
                out["reason"] = "No statement in the status paragraph; using a later STATE.md section."
            elif epols == {"positive"}:
                status = "reported_positive"
            elif epols:
                status = "conflicting"
            else:
                status = "unknown"
    for f in findings:
        for s in _split_sentences(f.get("status") or ""):
            if sentence_polarity(s) == "positive":
                out["finding_signals"].append({"id": f["id"], "text": s, "path": f.get("primary"), "uncommitted": f.get("uncommitted", False)})
    if status == "reported_none" and out["finding_signals"]:
        status = "conflicting"
        out["reason"] = "STATE.md reports none, but a finding's status contains possible positive wording."
    out["status"] = status
    out["label"], out["explanation"] = LABELS[status]
    out["primary"] = (out["headline"] or [e for e in out["elsewhere"] if status != "reported_none" or e["polarity"] == "negative"] or [None])[0]
    return out


def _epoch(iso: str | None) -> float | None:
    if not iso:
        return None
    try:
        return datetime.fromisoformat(iso).timestamp()
    except ValueError:
        return None


def achievements(state: dict | None, findings: list[dict], commits: list[dict], manifest_ok_findings: set[str],
                 reviewed_through: str | None) -> dict:
    """Live feed of reported milestones (STATE.md) and finding records, newest first.

    Ordering key: newest git commit date among commit hashes cited in the item,
    else among commits touching the cited finding IDs, else (findings only) file
    mtime. Undated items keep their document order after dated ones.
    """
    by_prefix = [(c["hash"], c) for c in commits]

    def commit_for(h: str) -> dict | None:
        for full, c in by_prefix:
            if full.startswith(h):
                return c
        return None

    commits_for_wid: dict[str, list[dict]] = {}
    for c in commits:
        for w in c.get("finding_ids", []):
            commits_for_wid.setdefault(w, []).append(c)

    reported: list[dict] = []
    if state:
        seen: set[str] = set()
        cands = [("status paragraph", s) for s in _split_sentences(state.get("status_paragraph", ""))
                 if HASH_RE.search(s) and CHECKPOINT_VERB_RE.search(s)]
        cands += [("established milestones", b) for b in state.get("established_milestones", [])]
        for order, (section, text) in enumerate(cands):
            if text in seen:
                continue
            seen.add(text)
            hashes = HASH_RE.findall(text)
            resolved = [commit_for(h) for h in hashes]
            wids = wids_in(text)
            dates = [_epoch(c["commit_date"]) for c in resolved if c]
            if not dates:
                dates = [_epoch(c["commit_date"]) for w in wids for c in commits_for_wid.get(w, [])]
            dates = [d for d in dates if d is not None]
            reported.append({
                "text": text, "section": section, "order": order,
                "hashes": [{"short": h, "in_git": c is not None, "subject": c["subject"] if c else None} for h, c in zip(hashes, resolved)],
                "finding_ids": wids,
                "when": max(dates) if dates else None,
                "when_basis": "cited commit" if resolved and any(resolved) else ("commit touching cited finding" if dates else None),
                "evidence": "reported",
            })
    reported.sort(key=lambda r: (r["when"] is None, -(r["when"] or 0), -r["order"]))

    recent: list[dict] = []
    for f in findings:
        cs = commits_for_wid.get(f["id"], [])
        cdates = [d for d in (_epoch(c["commit_date"]) for c in cs) if d is not None]
        when = f.get("latest_mtime") if f.get("uncommitted") or not cdates else max(cdates)
        hints = {h["category"]: h["matched"] for h in f.get("hints", [])}
        recent.append({
            "id": f["id"], "title": f.get("title"), "status": f.get("status", ""), "status_from": f.get("status_from"),
            "path": f.get("primary"), "date": f.get("date"), "commits": f.get("commits", []),
            "uncommitted": f.get("uncommitted", False),
            "when": when, "when_basis": "file modified (uncommitted)" if f.get("uncommitted") else ("latest commit" if cdates else "file modified"),
            "review_phrase": hints.get("reviewed"),
            "pending_phrase": hints.get("pending"),
            "rejected_phrase": hints.get("rejected"),
            "in_reviewed_snapshot": f["id"] in manifest_ok_findings,
            "newer_than_reviewed_snapshot": bool(reviewed_through and f["id"].startswith("W") and f["id"] > reviewed_through),
        })
    recent.sort(key=lambda r: (r["when"] or 0, r["id"]), reverse=True)  # ties (same-second commits): higher ID first
    return {"reported": reported, "findings": recent}
