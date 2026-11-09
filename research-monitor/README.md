# research-monitor

A local, read-only, live page that answers one question for a general audience:
**can today's computers recover a Bitcoin private key from its public key, and has the
research in `dlp-research/` changed that?** It updates within about 5 seconds of a
repository change, without a restart.

It uses only the Python 3 standard library and plain HTML/CSS/JS, with no build step,
no dependencies, and no network access at runtime. It never writes to `dlp-research/`.

## What the page shows

**Main view** (fits on roughly one screen):

- **Verdict**: for example "No — still far out of reach". It is computed from the current
  best work estimate at the published RTX 5090 rate with the default fleet of 10^6 GPUs.
- **Research status**: one line derived live from STATE.md (see *Outcome* below), e.g.
  "No verified improvement from this research — the estimate is unchanged."
- **Illustrative time to recover one key**, in words ("559 trillion years"), in scientific
  notation, and as a multiple of the age of the universe.
- **Logarithmic time scale**, labelled as logarithmic, with markers for 1 year, the age of
  the universe and the selected scenario. An assumed scenario is drawn as a dashed marker.
- **Controls**: GPU count (1 to 10^9, logarithmic slider), GPU model, and speed per GPU.
- **Has this research changed the estimate?** Bars compare the published method with the
  best *verified* research result in the same units. They stay identical, with "No change
  to the estimate", until a reviewed comparable result exists.
- **What would change it?** A faster algorithm, versus more or faster hardware, which only
  divides the time.
- A live indicator ("Live" / "Stale" / "Disconnected") and the time of the last data update.

**"How this estimate works & evidence"** is a collapsed drawer. It holds the formula,
assumptions and sources, the literal STATE.md outcome sentences, research activity,
complexity references and the reviewed snapshot, the frontier, the commit timeline,
findings, toy results, data freshness and the read-only source viewer. Nothing on the
main view counts theorems, commits or files.

### Hardware choices never invent a benchmark

| Choice | Speed used | Label shown |
|---|---|---|
| RTX 5090 | 19.3e9 steps/s, as reported by the RCKangaroo README | "Extrapolated from reported RTX 5090 speed" |
| RTX 5090 at 10×/100×/1000× | reference × multiplier | "Assumed … — what-if, not measured" |
| H200 / B200 | **none**: the result reads "Unknown" until you pick an assumed multiplier | "Not benchmarked", or "Assumed N× RTX 5090 speed — not a B200 benchmark" |
| Custom | a rate you have measured | "Your rate: …" |

No reliable public secp256k1 rho/kangaroo benchmark was found for H200 or B200. NVIDIA's reference
specs give AI FLOPS, memory and bandwidth, and these do not convert into this workload.
The manifest stores `ops_per_sec: null` for both. Faster or more GPUs only change the
constant: 2^128 / 19.3e9 is about 5.59e20 GPU-years. That is 5.59e14 years on 10^6 GPUs,
or 5.59e12 years on 10^6 GPUs if each is assumed to be 100× faster.

### Baseline vs. current result

`manifest.json → estimator.current_result` is the only thing that can move the "current"
bar, and it is `null` today. For the bar to move, a curated entry must have `reviewed:
true`, `units: "group operations"`, a `log2_work`, and a `source`. Keyword claims in
STATE.md or in findings never change the number. A positive claim only changes the status
line, to "reported but not verified" (`static/estimator.js → comparison`).

## Run

```bash
cd research-monitor
./run.sh                    # foreground, http://127.0.0.1:8765/
./start-bg.sh --port 8765   # detached; PID in .run/server.pid, log in .run/server.log
./stop.sh                   # stop the detached server
./run.sh --port 0           # any free port (printed on start)
```

Options: `--repo` (git root, default parent dir), `--research-dir` (default
`dlp-research`), `--interval` (poll seconds, default 5), `--host` (default
`127.0.0.1`), `--allow-host NAME` (extra accepted `Host` header, e.g. a proxy).

## Test

```bash
./test.sh   # 51 Python unittest cases (temp fixture git repos) + 10 node:test cases
```

The tests never touch live research files. They cover parsing, snapshots, missing or
corrupt sources, git failures, path traversal and symlink escapes, `Host` checks, the
estimator arithmetic (Python and JS), every HTTP endpoint, and live refresh over SSE.
`tests/scenario.test.cjs` checks that H200/B200 give no number without an explicit
assumption and are never labelled measured. It also checks the 1×/100× multipliers and
1 vs. 10^6 GPU scaling, that the baseline stays flat for every outcome status unless a
reviewed comparable result exists, and the human-readable durations.
`tests/test_http.py` checks that the main view comes first and the evidence drawer is
collapsed.
The live-refresh tests write a new finding, then commit it, in a temporary repo. They also
rewrite STATE.md (negative → positive claim → deleted → appended milestone) under a running
server and check that the outcome and achievements feed follow each edit (`tests/test_live.py`).

## How data flows

```
poller thread (every 5 s)                      browser
  fingerprint = stat(allowlisted files)          EventSource /api/events
              + git rev-parse HEAD                 ├ "snapshot" {instance, version}  → GET /api/snapshot
              + git status --porcelain             └ "heartbeat" {last_poll_at, ok}  → live / stale / disconnected
  changed? → build_snapshot() → version++
```

- **Snapshot** (`monitor/snapshot.py`): copies text verbatim from `research/STATE.md`
  (phase, headline sentences, live work, next step, open/blocked sentences),
  `Audit.lean` (live `#print axioms` count vs. the count STATE.md claims), every
  `research/findings/W###-*` file (title, Date, `Status:`/`Verdict:` line, sections),
  proposals, Lean modules, and `git log`/`git status`.
- **Hints, not classifications.** The Findings table shows keyword hints taken from
  each finding's own title and Status text. Each hint shows the exact phrase that
  matched, and positive hints are suppressed when negated ("not an accepted …
  experimental finding"). Findings with no keyword match say "unclassified". The
  research team never classified these findings; the hints are automatic.
- **Manifest** (`manifest.json`): this is the only curated content. It frames the
  complexity references (with sources) and states each established result's
  *units and scope*, so toy counts, wrapper calls, lookup probes and word-machine
  units are never presented as end-to-end speedups. On every refresh the server
  re-checks each entry's verbatim quote, theorem names, and finding IDs against the
  live files. Stale entries are flagged in the UI, and so are findings newer than
  the manifest.
- **Liveness:** the UI shows the last successful poll and the latest repository
  change as separate values. It shows *Stale* when there has been no event for
  max(3×interval, 12 s) or the last poll failed, and *Disconnected* when the SSE
  connection drops. A server `instance` id makes the UI reload after a restart.
  When a poll fails, the server keeps serving the last good snapshot and reports the
  error.

## What is live vs. manually reviewed

| Part of the page | Source | Updates |
|---|---|---|
| **Main-view status line** | outcome derived from STATE.md (`monitor/live.py`) | every refresh |
| **Main-view numbers** (verdict, time, bars) | `manifest.json` estimator: published reference + `current_result` (null) | manual only |
| Drawer: phase, headline sentences, open/blocked sentences, live work | STATE.md, verbatim | every refresh |
| Drawer: research activity | STATE.md status-paragraph checkpoint sentences + milestones section; finding records; git log | every refresh |
| Findings table, timeline, sources, audit count | finding files, git, Audit.lean | every refresh |
| Reviewed snapshot cards, repo-bounds table in Complexity | `manifest.json` (hand-curated through `reviewed_findings_through`) | manual; quotes/theorems re-checked every refresh, newer findings flagged |
| Classical references, estimator defaults | `manifest.json` (textbook/published sources) | static |

**Outcome.** Nothing is hardcoded. On each snapshot the server finds STATE.md
sentences that discuss an end-to-end speedup, break or verified improvement. It decides
by keyword whether each one is negated ("No faster …", "… remains open", or a
report-style "Verified improvement …: NONE"). It reports one of four states:
*None reported*, *Claim reported — evidence review required*, *Conflicting — not
assessed*, or *Unknown — not assessed*. The status paragraph takes priority. A
later-section sentence is used only when the status paragraph says nothing, and the UI
says so. If STATE.md is missing or has no such sentence, the result is *Unknown*. If a
finding's own status line reads as a positive speedup claim while STATE.md says none,
the result is *Conflicting*. The main view shows a one-line summary of the state. The
drawer shows the literal sentences, their section, and the STATE.md modification time. A
positive reading is never labelled verified, and it never changes the estimate.

**Research activity (drawer).** Two lists, newest first:
1. *Reported milestones*: STATE.md status-paragraph sentences that cite a commit hash
   with a verb such as committed/verified/accepted, plus every bullet in a heading
   matching `milestone|achievement`. Each item is dated by the git commit it cites, or
   else by commits touching the finding IDs it cites. Cited hashes missing from
   `git log` are flagged. Every item is tagged "reported · STATE.md" because it is the
   coordinator's text.
2. *Latest finding records*: ordered by latest commit, or by file time for uncommitted
   drafts. Chips show provenance only: uncommitted draft or committed record, a
   status-text phrase such as "verified"/"PASS" quoted from the finding itself, and
   whether the finding is in the reviewed snapshot.

Naming variants are tolerated: `w21_x.md`/`W0021-x.md` → `W021`; `**Status:**`;
`## Established Milestones`/`Achievements`; `## Active work`.

## Security model

- Binds to `127.0.0.1` by default. Requests whose `Host` header is not loopback get
  421 (DNS-rebinding guard). Only GET and HEAD are served; other methods get 405.
- `/api/source?path=` serves **only** allowlisted shapes under the research dir:
  top-level docs, `research/STATE.md`, `research/findings/*.{md,json,txt}`,
  `research/proposals/**/*.md`, `research/artifacts/*`, `Research/*.lean` and
  `scripts/*.{py,sh,lean}`. Requests with `..`, absolute paths, or hidden names are
  rejected, as is anything that resolves through a symlink (realpath check plus
  `O_NOFOLLOW`). Reads are capped at 2 MiB. `.git`, `.tools`, `.lake` and arbitrary
  files are never served.
- Git runs with fixed argument lists (no shell), a 5 s timeout, a 4 MiB output cap and
  `GIT_OPTIONAL_LOCKS=0`, so it never takes the index lock from working agents.
  `/api/commit` accepts only a hex hash that `git cat-file` verifies.
- The UI inserts all repository content with `textContent`/DOM nodes, never
  `innerHTML`. The minimal Markdown renderer links only `http(s)` URLs. A strict CSP
  is in force (`script-src 'self'`, no inline styles or scripts).

## Runtime estimator

time = work / (GPUs × ops/s/GPU). `static/estimator.js` (scenarios, comparison and
wording) and `monitor/estimate.py` (arithmetic) produce the same numbers. The arithmetic is done in log10 space, so inputs up
to 2^4096 are safe. With the defaults (2^128 work, 19.3e9 ops/s from the RCKangaroo
README's reported RTX 5090 rate) the results are **5.59e20 years on 1 GPU** and
**5.59e14 years on 1e6 GPUs**, which is 5.59e20 GPU-years in both cases.

This is an *illustrative extrapolation*. It assumes perfect linear scaling and no
distinguished-point or communication overhead, and uses expected rather than worst-case
work. The RCKangaroo rate counts bounded-range kangaroo steps, which are only
approximately rho group additions. The workload is key **recovery**, not key
generation. The estimator gives no estimate for any repository algorithm, because none
has a validated mapping from its cost units to GPU operations.

Sources: <https://github.com/RetiredC/RCKangaroo>, <https://safecurves.cr.yp.to/rho.html>
(0.886·√ℓ additions, which SafeCurves lists as 2^127.8 for secp256k1).

## Limits

- The outcome polarity and the status chips come from keyword heuristics. They can
  misread unusual phrasing (e.g. a positive claim worded with "not"). That is why the
  literal sentence is always available in the drawer and nothing is ever marked
  verified. The monitor does not review proofs or experiments. It cannot interpret new
  mathematical claims by itself: a real improvement reaches the main-view numbers only
  through a hand-reviewed `current_result` entry.
- The verdict thresholds are fixed: at least 1,000 years means "far out of reach",
  1–1,000 years means "enormous effort", and under 1 year means "within reach". They
  use the published RTX 5090 rate on 10^6 GPUs.
- There is no H200/B200 number until someone publishes a benchmark for this workload.
  Their multipliers are user assumptions.
- STATE.md items without a resolvable commit or finding ID are listed after the dated
  items, in document order.
- The reviewed-snapshot cards and the repo-bounds rows in the Complexity table change
  only when `manifest.json` is edited by hand. Newer findings are flagged, but their
  units and scope are not reviewed automatically.
- Manifest edits and backend code changes need a server restart (`./stop.sh && ./start-bg.sh --port 8765`).
  Static files and research data do not.
