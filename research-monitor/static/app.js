/* Research monitor UI. All repository content is inserted with textContent /
 * DOM nodes only — never innerHTML — because findings are untrusted text. */
(function () {
  "use strict";

  var state = {
    snap: null, meta: null, version: -1, instance: null,
    lastEventAt: 0, connected: false, pollInterval: 5,
    seenFindings: null, seenCommits: null, newFindings: {}, newCommits: {},
    es: null, fallbackTimer: null
  };

  // ---------- DOM helpers ----------
  function $(id) { return document.getElementById(id); }
  function el(tag, attrs) {
    var node = document.createElement(tag);
    if (attrs) {
      for (var k in attrs) {
        if (!Object.prototype.hasOwnProperty.call(attrs, k) || attrs[k] == null || attrs[k] === false) continue;
        if (k === "text") node.textContent = attrs[k];
        else if (k === "class") node.className = attrs[k];
        else if (k === "style") node.style.cssText = attrs[k]; // CSSOM is allowed under CSP; style attributes are not
        else if (k === "onclick") node.addEventListener("click", attrs[k]);
        else node.setAttribute(k, attrs[k]);
      }
    }
    for (var i = 2; i < arguments.length; i++) append(node, arguments[i]);
    return node;
  }
  function append(node, child) {
    if (child == null || child === false) return;
    if (Array.isArray(child)) { child.forEach(function (c) { append(node, c); }); return; }
    node.appendChild(typeof child === "string" || typeof child === "number" ? document.createTextNode(String(child)) : child);
  }
  function replace(node, children) { node.replaceChildren(); append(node, children); }
  function safeUrl(u) { return /^https?:\/\/[^\s"'<>]+$/i.test(u || "") ? u : null; }
  function extLink(url, label) {
    var u = safeUrl(url);
    return u ? el("a", { href: u, target: "_blank", rel: "noopener noreferrer" }, label || u) : el("span", { text: label || "" });
  }
  function fmtTime(iso) {
    if (!iso) return "—";
    var d = new Date(iso);
    if (isNaN(d)) return iso;
    return d.toLocaleString(undefined, { year: "numeric", month: "short", day: "2-digit", hour: "2-digit", minute: "2-digit", second: "2-digit" });
  }
  function ago(iso) {
    if (!iso) return "";
    var s = Math.round((Date.now() - new Date(iso).getTime()) / 1000);
    if (!isFinite(s)) return "";
    if (s < 5) return "just now";
    if (s < 90) return s + " s ago";
    if (s < 5400) return Math.round(s / 60) + " min ago";
    if (s < 172800) return Math.round(s / 3600) + " h ago";
    return Math.round(s / 86400) + " d ago";
  }
  function sourceButton(path, label, cls) {
    return el("button", { type: "button", class: cls || "linkish", title: "Open " + path, onclick: function () { openSource(path); } }, label || path);
  }
  function commitButton(short) {
    return el("button", { type: "button", class: "chip", title: "Show commit " + short, onclick: function () { openCommit(short); } }, short);
  }
  function findingButton(id) {
    var f = findingById(id);
    if (!f || !f.primary) return el("span", { class: "chip", text: id });
    return el("button", { type: "button", class: "chip", title: f.title, onclick: function () { openSource(f.primary); } }, id);
  }
  function findingById(id) {
    var list = (state.snap && state.snap.findings) || [];
    for (var i = 0; i < list.length; i++) if (list[i].id === id) return list[i];
    return null;
  }

  // ---------- Connection / live status ----------
  function setConn(kind, text) {
    var pill = $("conn");
    pill.className = "pill pill-" + kind;
    $("conn-text").textContent = text;
    var banner = $("banner");
    if (kind === "down") {
      banner.hidden = false; banner.className = "banner";
      banner.textContent = "Disconnected from the monitor server — showing the last snapshot received" +
        (state.meta && state.meta.last_poll_at ? " (last successful poll " + fmtTime(state.meta.last_poll_at) + ")" : "") + ". Retrying…";
    } else if (kind === "stale") {
      banner.hidden = false; banner.className = "banner stale";
      banner.textContent = text + ". The data below may be out of date.";
    } else {
      banner.hidden = true;
    }
  }
  function updateMeta() {
    var m = state.meta, s = state.snap;
    if (m) $("m-poll").textContent = m.last_poll_ok ? fmtTime(m.last_poll_at) + " (" + ago(m.last_poll_at) + ")" : "FAILED: " + (m.last_poll_error || "unknown");
    if (s && s.repo) {
      $("m-change").textContent = fmtTime(s.repo.latest_repo_change) + " (" + ago(s.repo.latest_repo_change) + ")";
      $("data-updated").textContent = "Data updated " + ago(s.repo.latest_repo_change);
      var h = s.repo.head || {};
      $("m-head").textContent = h.hash ? h.hash.slice(0, 7) + (h.branch ? " · " + h.branch : "") : "unavailable";
    }
  }
  function tick() {
    updateMeta();
    if (!state.connected) return;
    var silent = (Date.now() - state.lastEventAt) / 1000;
    var limit = Math.max(3 * state.pollInterval, 12);
    if (silent > limit) setConn("stale", "Stale: no update from server for " + Math.round(silent) + " s");
    else if (state.meta && !state.meta.last_poll_ok) setConn("stale", "Server reachable, but last repository poll failed");
    else { setConn("live", "Live"); $("conn").title = "Checking the research repository every " + state.pollInterval + " s"; }
  }
  function onStatus(meta) {
    state.meta = meta; state.lastEventAt = Date.now(); state.connected = true;
    if (meta.poll_interval_s) state.pollInterval = meta.poll_interval_s;
    if (meta.version !== state.version || meta.instance !== state.instance) loadSnapshot();
    tick();
  }
  function connect() {
    if (!window.EventSource) return startFallback();
    var es = new EventSource("/api/events");
    state.es = es;
    es.addEventListener("snapshot", function (e) { try { onStatus(JSON.parse(e.data)); } catch (_) {} });
    es.addEventListener("heartbeat", function (e) { try { onStatus(JSON.parse(e.data)); } catch (_) {} });
    es.onopen = function () { state.connected = true; state.lastEventAt = Date.now(); tick(); };
    es.onerror = function () {
      state.connected = false;
      setConn("down", "Disconnected · retrying");
      if (es.readyState === 2) { setTimeout(connect, 3000); }
    };
  }
  function startFallback() {
    if (state.fallbackTimer) return;
    var poll = function () {
      fetch("/api/status", { cache: "no-store" }).then(function (r) { return r.json(); })
        .then(onStatus).catch(function () { state.connected = false; setConn("down", "Disconnected · retrying"); });
    };
    poll(); state.fallbackTimer = setInterval(poll, 5000);
  }
  var loading = false;
  function loadSnapshot() {
    if (loading) return; loading = true;
    fetch("/api/snapshot", { cache: "no-store" }).then(function (r) {
      if (!r.ok) throw new Error("HTTP " + r.status);
      return r.json();
    }).then(function (data) {
      state.meta = data.meta; state.version = data.meta.version; state.instance = data.meta.instance;
      if (data.snapshot && data.snapshot.repo) { trackNew(data.snapshot); state.snap = data.snapshot; render(); }
    }).catch(function (err) {
      setConn("stale", "Snapshot fetch failed (" + err.message + ")");
    }).then(function () { loading = false; updateMeta(); });
  }
  function trackNew(snap) {
    var fids = snap.findings.map(function (f) { return f.id; });
    var cids = snap.commits.map(function (c) { return c.hash; });
    if (state.seenFindings) {
      fids.forEach(function (id) { if (state.seenFindings.indexOf(id) < 0) state.newFindings[id] = true; });
      cids.forEach(function (id) { if (state.seenCommits.indexOf(id) < 0) state.newCommits[id] = true; });
    }
    state.seenFindings = fids; state.seenCommits = cids;
  }

  // ---------- Rendering ----------
  function render() {
    var s = state.snap;
    [renderMain, renderOverview, renderAchievements, renderEvidence, renderComplexity, renderFrontier, renderTimeline, renderFindings, renderResults, renderSources, renderEstimatorMeta]
      .forEach(function (fn) {
        try { fn(s); } catch (e) { if (window.console) console.error(fn.name, e); }
      });
  }

  function tile(label, value, note) {
    return el("div", { class: "tile" }, el("div", { class: "label", text: label }), el("div", { class: "value", text: value == null ? "—" : String(value) }), note ? el("div", { class: "note" }, note) : null);
  }

  function renderOverview(s) {
    var st = s.state;
    var body = $("overview-body");
    if (!st) { replace(body, el("p", { class: "error", text: "research/STATE.md is missing or unreadable; no phase can be shown." })); return; }
    var latestFinding = s.findings.slice().sort(function (a, b) { return (b.latest_mtime || 0) - (a.latest_mtime || 0); })[0];
    var auditNote = s.audit.claimed_in_state == null ? "no count stated in STATE.md" :
      (s.audit.claimed_in_state === s.audit.count ? "matches STATE.md claim (" + s.audit.claimed_in_state + ")" :
        "STATE.md states " + s.audit.claimed_in_state + " — differs from live Audit.lean");
    var wt = s.repo.working_tree || [];
    replace(body, [
      el("p", { class: "phase" }, "Phase: ", el("span", { text: st.phase || "(no Status line found)" })),
      el("div", { class: "headline", role: "note" },
        el("strong", { text: "Headline outcome (verbatim from STATE.md):" }),
        (st.headline_sentences && st.headline_sentences.length ? st.headline_sentences : ["(no headline sentence found)"]).map(function (t) { return el("p", { text: t }); })),
      el("details", null, el("summary", { text: "Full STATE.md status paragraph" }), el("p", { class: "small", text: st.status_paragraph }), sourceButton("research/STATE.md", "Open STATE.md")),
      el("div", { class: "tiles" },
        tile("Named theorem audits (live Audit.lean)", s.audit.count, auditNote),
        tile("Finding records", s.findings.length, latestFinding ? ["latest touched: ", findingButton(latestFinding.id)] : null),
        tile("Commits", s.repo.commit_count, s.repo.latest_commit ? ["latest ", commitButton(s.repo.latest_commit.short), " " + ago(s.repo.latest_commit.commit_date)] : null),
        tile("Uncommitted research files", wt.length, wt.length ? "in-progress work, not yet integrated" : "working tree clean"),
        outcomeTile(s.outcome)
      ),
      outcomeBox(s.outcome),
      s.warnings && s.warnings.length ? el("div", { class: "warn-box small", style: null }, el("strong", { text: "Data warnings: " }), el("ul", { class: "list-tight" }, s.warnings.map(function (w) { return el("li", { text: w }); }))) : null
    ]);
  }

  // Attributed, recomputed-every-snapshot outcome. Never a hardcoded verdict.
  var OUTCOME_CLASS = { reported_none: "o-none", reported_positive: "o-positive", conflicting: "o-conflict", unknown: "o-unknown" };
  function outcomeTile(o) {
    o = o || { status: "unknown", label: "Unknown — not assessed" };
    return el("div", { class: "tile outcome-tile " + (OUTCOME_CLASS[o.status] || "o-unknown"), id: "outcome-tile" },
      el("div", { class: "label", text: "End-to-end speedup / break — as reported by live STATE.md" }),
      el("div", { class: "value small-value", text: o.label }),
      el("div", { class: "note" }, o.source_mtime ? "STATE.md modified " + fmtTime(o.source_mtime) + " · " : "", "keyword-derived; not reviewed by this monitor"));
  }
  function outcomeBox(o) {
    if (!o) return null;
    var quotes = (o.headline || []).concat(o.status === "reported_none" ? [] : (o.elsewhere || []).filter(function (e) { return e.polarity === "positive"; }));
    if (!quotes.length && o.primary) quotes = [o.primary];
    return el("div", { class: "outcome-box " + (OUTCOME_CLASS[o.status] || "o-unknown"), role: "note", "aria-label": "Outcome source sentences" },
      el("strong", { text: o.label + ". " }), el("span", { class: "small", text: o.explanation || "" }),
      o.reason ? el("p", { class: "small", text: o.reason }) : null,
      quotes.length ? el("ul", { class: "list-tight" }, quotes.map(function (q) {
        return el("li", null, "“", el("span", { text: q.text }), "” ", el("span", { class: "muted small", text: "— " + (q.section || "STATE.md") + (q.polarity === "positive" ? " · reads as positive claim (unreviewed)" : "") }));
      })) : el("p", { class: "small muted", text: "No sentence about an end-to-end speedup or break found." }),
      (o.finding_signals || []).length ? el("div", { class: "small" }, el("strong", { text: "Possible positive wording in findings (unreviewed, evidence review required): " }),
        el("ul", { class: "list-tight" }, o.finding_signals.map(function (f) { return el("li", null, findingButton(f.id), f.uncommitted ? el("span", { class: "chip dirty", text: "uncommitted" }) : null, " “", el("span", { text: f.text }), "”"); }))) : null,
      el("div", { class: "small" }, sourceButton(o.source || "research/STATE.md", "Open STATE.md"), o.source_mtime ? el("span", { class: "muted", text: " · modified " + fmtTime(o.source_mtime) + " (" + ago(o.source_mtime) + ")" }) : null));
  }

  // Live feed: reported milestones (STATE.md) + newest finding records. Labels describe provenance only.
  var FEED_SHOWN = 6;
  function renderAchievements(s) {
    var a = s.achievements || { reported: [], findings: [] };
    function when(r) { return r.when ? fmtTime(new Date(r.when * 1000).toISOString()) : "undated"; }
    function reportedItem(r) {
      return el("li", { class: "feed-item" },
        el("div", { class: "feed-meta" }, el("span", { class: "chip prov-reported", title: "Text written by the research coordinator in STATE.md (" + r.section + "); not independently checked by this monitor", text: "reported · STATE.md" }),
          el("span", { class: "muted small", title: r.when_basis || "", text: when(r) })),
        el("div", { class: "feed-text", text: r.text }),
        el("div", null, (r.hashes || []).map(function (h) {
          return h.in_git ? commitButton(h.short) : el("span", { class: "chip bad", title: "hash cited in STATE.md but not found in git log", text: h.short + " ?" });
        }), (r.finding_ids || []).map(findingButton)));
    }
    function findingItem(f) {
      var chips = [];
      chips.push(f.uncommitted ? el("span", { class: "chip dirty", text: "uncommitted draft" }) : el("span", { class: "chip", title: "record committed to git; content not re-verified by the monitor", text: "committed record" }));
      if (state.newFindings[f.id]) chips.push(el("span", { class: "chip new", text: "new" }));
      if (f.review_phrase) chips.push(el("span", { class: "chip hint-reviewed", title: "Keyword in the finding's own status text — a claim by the authors, not monitor verification", text: "status text says “" + f.review_phrase + "”" }));
      if (f.pending_phrase) chips.push(el("span", { class: "chip hint-pending", text: "status text says “" + f.pending_phrase + "”" }));
      if (f.rejected_phrase) chips.push(el("span", { class: "chip hint-rejected", text: "status text says “" + f.rejected_phrase + "”" }));
      if (f.in_reviewed_snapshot) chips.push(el("span", { class: "chip ok", title: "Cited by a curated card whose quote/theorems were re-checked against live files", text: "in reviewed snapshot" }));
      else if (f.newer_than_reviewed_snapshot) chips.push(el("span", { class: "chip", title: "Newer than the curated manifest; units/scope not yet reviewed for the complexity cards", text: "not in reviewed snapshot" }));
      var status = (f.status || "(no status line)").replace(/\*\*/g, "");
      return el("li", { class: "feed-item" },
        el("div", { class: "feed-meta" }, findingButton(f.id), el("span", { class: "muted small", title: f.when_basis, text: when(f) + " · " + f.when_basis })),
        el("div", { class: "feed-title" }, f.path ? sourceButton(f.path, f.title) : el("span", { text: f.title })),
        el("div", { class: "feed-text small" }, el("span", { class: "muted", text: (f.status_from && f.status_from !== "Status line" ? f.status_from : "Status") + ": " }), status.length > 260 ? status.slice(0, 257) + "…" : status),
        el("div", null, chips));
    }
    function list(items, fn, label) {
      var head = items.slice(0, FEED_SHOWN), rest = items.slice(FEED_SHOWN);
      return [el("ol", { class: "feed" }, head.map(fn)),
        rest.length ? el("details", null, el("summary", { text: "Show " + rest.length + " older " + label }), el("ol", { class: "feed" }, rest.map(fn))) : null];
    }
    replace($("achievements-body"), el("div", { class: "cols" },
      el("div", null, el("h3", { text: "Reported milestones (STATE.md, newest first)" }),
        el("p", { class: "small muted", text: "Verbatim sentences from the STATE.md status paragraph and its milestones section, dated by the git commit they cite. Reported by the research coordinator; the monitor checks only that cited hashes exist." }),
        a.reported.length ? list(a.reported, reportedItem, "milestones") : el("p", { class: "muted", text: "No milestone sentences found in STATE.md." })),
      el("div", null, el("h3", { text: "Latest finding records (live files)" }),
        el("p", { class: "small muted", text: "Newest first by latest commit (or file time for uncommitted drafts). Status text is the finding's own; chips show provenance, not monitor verification." }),
        a.findings.length ? list(a.findings, findingItem, "findings") : el("p", { class: "muted", text: "No finding records found." }))));
  }

  var CATS = [
    ["proved", "✓", "Proved (Lean, in stated units)"],
    ["experiment", "E", "Experimentally observed (toy scale)"],
    ["negative", "N", "Negative / counterexample results"],
    ["rejected", "✕", "Rejected proposals"],
    ["open", "?", "Open / blocked (unknown cost)"]
  ];
  function renderEvidence(s) {
    var items = (s.repo_results || []).slice();
    var order = CATS.map(function (c) { return c[0]; });
    items.sort(function (a, b) { return order.indexOf(a.category) - order.indexOf(b.category); });
    var newer = (s.manifest && s.manifest.findings_newer_than_manifest) || [];
    replace($("evidence-body"), [
      el("div", { class: "ev-legend", "aria-label": "Categories" }, CATS.map(function (c) {
        var n = items.filter(function (it) { return it.category === c[0]; }).length;
        return el("span", null, el("span", { class: "cat-icon cat-" + c[0], "aria-hidden": "true", text: c[1] }), c[2] + " (" + n + ")");
      })),
      el("p", { class: "small" }, el("span", { class: "chip" , text: "reviewed snapshot" }), " Manually curated at commit ", el("code", { text: (s.manifest && s.manifest.reviewed_at_commit) || "?" }), " (" + ((s.manifest && s.manifest.reviewed_on) || "?") + "), findings through " + ((s.manifest && s.manifest.reviewed_findings_through) || "?") + ". Not updated automatically; quotes/theorems are re-checked live."),
      newer.length ? el("div", { class: "warn-box small" }, "Newer findings not covered by this reviewed snapshot (through " + s.manifest.reviewed_findings_through + "): ", newer.map(findingButton), " — see “Latest achievements” above; their units and scope have not been reviewed for these cards.") : null,
      el("div", { class: "evidence-grid", style: "margin-top:0.75rem" }, items.map(evCard))
    ]);
  }
  function evCard(it) {
    var v = it.verification || {}, ev = it.evidence || {};
    var problems = [];
    if (!v.source_present) problems.push("source missing");
    else if (!v.quote_found) problems.push("quote no longer found in source");
    (v.theorems_missing || []).forEach(function (t) { problems.push("theorem not in Audit.lean: " + t); });
    (v.findings_missing || []).forEach(function (t) { problems.push("finding missing: " + t); });
    var cat = CATS.filter(function (c) { return c[0] === it.category; })[0] || [it.category, "·", it.category];
    return el("article", { class: "ev-card" },
      el("div", { class: "head" }, el("span", { class: "cat-icon cat-" + cat[0], "aria-hidden": "true", text: cat[1] }),
        el("div", null, el("div", { class: "kind", text: cat[2] }), el("div", { class: "t", text: it.title }))),
      el("dl", null,
        el("dt", { text: "Bound" }), el("dd", { text: it.bound }),
        el("dt", { text: "Units" }), el("dd", { text: it.unit }),
        el("dt", { text: "Scope" }), el("dd", { text: it.scope }),
        el("dt", { text: "Not shown" }), el("dd", { text: it.not_established })),
      ev.quote ? el("blockquote", null, "“" + ev.quote + "” — ", ev.source ? sourceButton(ev.source, ev.source) : null) : null,
      el("div", null,
        (ev.findings || []).map(findingButton),
        (ev.theorems || []).map(function (t) { return el("span", { class: "chip mono", title: "Lean theorem audited in Audit.lean", text: t.replace(/^Research\./, "") }); }),
        el("span", { class: "chip " + (v.ok ? "ok" : "bad"), title: problems.join("; ") || "quote and theorem names found in live files", text: v.ok ? "✓ evidence re-checked live" : "⚠ " + problems.join("; ") })));
  }

  function renderComplexity(s) {
    var c = s.complexity || {}, man = s.manifest || {}, prob = man.problem || {};
    var refs = c.references || [];
    var rows = refs.map(function (r) {
      return el("tr", null,
        el("td", null, el("strong", { text: r.method })),
        el("td", { text: r.formula }),
        el("td", { class: "num", text: r.log2_ops == null ? "n/a" : "2^" + r.log2_ops.toFixed(1) }),
        el("td", { text: r.memory }),
        el("td", { text: r.status }),
        el("td", null, r.source ? extLink(r.source.url, r.source.label) : null));
    });
    var repoRows = (s.repo_results || []).map(function (r) {
      return el("tr", { class: r.category === "open" ? "unknown" : null },
        el("td", { text: r.title }), el("td", { text: r.category }), el("td", { text: r.unit }), el("td", { text: r.bound }));
    });
    // log2-scale bars, 0..ceil to 256
    var maxLog = 256;
    var barItems = refs.filter(function (r) { return r.log2_ops != null; }).map(function (r) { return { label: r.method, v: r.log2_ops }; });
    barItems.push({ label: "Repo algorithms (end-to-end)", v: null });
    var bars = el("div", { class: "bars", role: "img", "aria-label": "Work in log2 group operations per method; repo algorithms have unknown end-to-end cost" },
      barItems.map(function (b) {
        return el("div", { class: "bar-row", title: b.v == null ? "unknown — no end-to-end cost established" : b.label + ": 2^" + b.v.toFixed(2) + " operations" },
          el("span", { text: b.label }),
          el("div", { class: "bar-track" }, el("div", { class: "bar" + (b.v == null ? " hatched" : ""), style: "width:" + (b.v == null ? 100 : Math.max(0.5, 100 * b.v / maxLog)) + "%" })),
          el("span", { class: "mono small", text: b.v == null ? "unknown" : "2^" + b.v.toFixed(1) }));
      }),
      el("div", { class: "axis" }, el("span", { class: "lbl", text: "log2(operations) →" }), el("div", { class: "ticks" }, ["0", "64", "128", "192", "256"].map(function (t) { return el("span", { text: t }); })), el("span")));
    replace($("complexity-body"), [
      el("p", null, el("strong", { text: prob.name || "Problem" }), ": ", prob.statement || ""),
      el("p", { class: "small" }, "Group order n (parsed live from ", sourceButton(prob.order_source || "Research/Secp256k1.lean"), "): ",
        el("code", { text: c.order_hex || "not parsed" }), " — ", c.order_bits ? c.order_bits + " bits, log2 n ≈ " + c.order_log2.toFixed(6) : "unknown"),
      el("p", { class: "small muted", text: prob.not_key_generation || "" }),
      el("h3", { text: "Classical / generic references for full-size key recovery" }),
      el("div", { class: "table-wrap" }, el("table", null,
        el("thead", null, el("tr", null, ["Method", "Work", "log2 ops (secp256k1)", "Memory", "Status", "Source"].map(function (h) { return el("th", { scope: "col", text: h }); }))),
        el("tbody", null, rows))),
      bars,
      el("p", { class: "small" }, el("strong", { text: "Reference used below: 2^" + (c.rounded_reference_log2 || 128) + " group operations. " }), c.rounded_reference_note || ""),
      el("h3", { text: "Bounds the repo has actually established (scope & units)" }),
      el("p", { class: "small muted", text: "Do not compare these units with the GPU-operation units above: equality tests, lookup queries and abstract word actions are not end-to-end group operations, and toy-curve counts do not extrapolate." }),
      el("div", { class: "table-wrap" }, el("table", null,
        el("thead", null, el("tr", null, ["Result", "Kind", "Units", "Bound"].map(function (h) { return el("th", { scope: "col", text: h }); }))),
        el("tbody", null, repoRows)))
    ]);
  }

  function renderFrontier(s) {
    var st = s.state || {};
    var wt = s.repo.working_tree || [];
    replace($("frontier-body"), el("div", { class: "cols" },
      el("div", { class: "prose" }, el("h3", { text: "Current live work (STATE.md)" }),
        st.current_live_work && st.current_live_work.length ? el("ul", { class: "list-tight" }, st.current_live_work.map(function (t) { return el("li", { text: t }); })) : el("p", { class: "muted", text: "No “Current live work” section found." }),
        el("h3", { text: "Next distinct step (STATE.md)" }),
        el("p", { class: "small", text: st.next_step || "—" })),
      el("div", { class: "prose" }, el("h3", { text: "Open / blocked statements (verbatim)" }),
        el("ul", { class: "list-tight" }, (st.open_sentences || []).map(function (t) { return el("li", { text: t }); })),
        el("h3", { text: "Uncommitted research files (in progress)" }),
        wt.length ? el("ul", { class: "list-tight" }, wt.map(function (w) {
          return el("li", null, el("span", { class: "chip dirty", text: w.state }), " ", sourceButton(w.path));
        })) : el("p", { class: "muted small", text: "Working tree clean." }))));
  }

  function renderTimeline(s) {
    var items = [];
    var wt = s.repo.working_tree || [];
    if (wt.length) {
      items.push(el("li", { class: "wip" }, el("span", { class: "when", text: "now (uncommitted)" }), el("span", { class: "chip dirty", text: wt.length + " files" }),
        el("span", null, "Work in progress: ", wt.map(function (w) { return w.path; }).join(", "))));
    }
    s.commits.forEach(function (c, i) {
      items.push(el("li", null,
        el("span", { class: "when", title: c.commit_date, text: fmtTime(c.commit_date) }),
        el("span", null, commitButton(c.short)),
        el("span", null, state.newCommits[c.hash] ? el("span", { class: "chip new", text: "new" }) : null, i === 0 ? el("span", { class: "chip", text: "HEAD" }) : null,
          el("span", { text: c.subject + " " }), c.finding_ids.map(findingButton))));
    });
    replace($("timeline-body"), items.length ? items : el("li", { class: "muted", text: "No commits readable." }));
  }

  function renderFindings(s) {
    var q = ($("f-search").value || "").toLowerCase();
    var hint = $("f-hint").value;
    var sel = $("f-hint");
    var cats = {};
    s.findings.forEach(function (f) { f.hints.forEach(function (h) { cats[h.category] = h.label; }); });
    var existing = Array.prototype.map.call(sel.options, function (o) { return o.value; });
    Object.keys(cats).sort().forEach(function (k) { if (existing.indexOf(k) < 0) sel.appendChild(el("option", { value: k, text: cats[k] })); });
    var rows = s.findings.filter(function (f) {
      if (hint && !f.hints.some(function (h) { return h.category === hint; })) return false;
      if (!q) return true;
      return (f.id + " " + f.title + " " + f.status).toLowerCase().indexOf(q) >= 0;
    }).slice().reverse().map(function (f) {
      return el("tr", null,
        el("td", null, el("strong", { text: f.id }), state.newFindings[f.id] ? el("span", { class: "chip new", text: "new" }) : null, f.uncommitted ? el("span", { class: "chip dirty", text: "uncommitted" }) : null),
        el("td", null, f.primary ? sourceButton(f.primary, f.title) : el("span", { text: f.title }),
          el("div", { class: "small muted" }, f.date ? f.date + " · " : "", f.files.map(function (fi) { return [sourceButton(fi.path, fi.path.split("/").pop(), "linkish small"), " "]; }))),
        el("td", { class: "small" }, el("span", { text: f.status || "(no status)" }), f.status_from && f.status_from !== "Status line" ? el("div", { class: "muted", text: "from " + f.status_from }) : null),
        el("td", null, f.hints.map(function (h) { return el("span", { class: "chip hint-" + h.category, title: "matched: “" + h.matched + "”" }, h.label, h.matched ? el("span", { class: "muted", text: " · “" + h.matched + "”" }) : null); })),
        el("td", null, f.commits.length ? f.commits.map(commitButton) : el("span", { class: "muted small", text: "none" })));
    });
    replace($("findings-body"), rows.length ? rows : el("tr", null, el("td", { colspan: "5", class: "muted", text: "No findings match." })));
  }

  function renderResults(s) {
    var blocks = (s.results || []).map(function (r) {
      var parts = [el("h3", null, findingButton(r.finding_id), " ", sourceButton(r.path, r.path.split("/").pop()))];
      if (r.error) parts.push(el("p", { class: "error", text: r.error }));
      if (r.fields) {
        parts.push(el("dl", { class: "small" }, Object.keys(r.fields).map(function (k) {
          return [el("dt", { class: "muted", text: k }), el("dd", { text: JSON.stringify(r.fields[k]) })];
        })));
      }
      if (r.table) {
        parts.push(el("div", { class: "table-wrap" }, el("table", null,
          el("thead", null, el("tr", null, r.table.columns.map(function (h) { return el("th", { scope: "col", text: h }); }))),
          el("tbody", null, r.table.rows.map(function (row) { return el("tr", null, r.table.columns.map(function (k) { return el("td", { class: "num", text: row[k] == null ? "—" : String(row[k]) }); })); })))));
      }
      if (r.lines) parts.push(el("pre", { class: "small", text: r.lines.join("\n") }));
      return el("div", { class: "ev-card" }, parts);
    });
    replace($("results-body"), blocks.length ? el("div", { class: "cols" }, blocks) : el("p", { class: "muted", text: "No results files found." }));
  }

  function renderSources(s) {
    var man = s.manifest || {};
    replace($("sources-body"), [
      el("p", { class: "small" }, "Snapshot built ", el("strong", { text: fmtTime(s.generated_at) }), " in " + s.build_ms + " ms. Latest file change: ",
        s.repo.latest_file_change ? sourceButton(s.repo.latest_file_change.path) : "—", s.repo.latest_file_change ? " at " + fmtTime(s.repo.latest_file_change.mtime) : "",
        ". Latest commit: ", s.repo.latest_commit ? commitButton(s.repo.latest_commit.short) : "—", s.repo.latest_commit ? " at " + fmtTime(s.repo.latest_commit.commit_date) : ""),
      el("p", { class: "small" }, "Curated manifest reviewed at commit ", el("code", { text: man.reviewed_at_commit || "?" }), " on " + (man.reviewed_on || "?") + ", findings through " + (man.reviewed_findings_through || "?") + ". ", el("span", { class: "muted", text: man.about || "" })),
      el("p", { class: "small muted", text: (s.sources || []).length + " allowlisted research files (read-only). Only these paths can be opened; .git internals, toolchains and other files are never served." }),
      el("div", { class: "scroll-box" }, el("table", null,
        el("thead", null, el("tr", null, ["File", "Modified", "Size", "Git"].map(function (h) { return el("th", { scope: "col", text: h }); }))),
        el("tbody", null, (s.sources || []).map(function (f) {
          var dirty = (s.repo.working_tree || []).filter(function (w) { return w.path === f.path; })[0];
          return el("tr", null, el("td", null, sourceButton(f.path)), el("td", { class: "small", text: fmtTime(f.mtime) }), el("td", { class: "num", text: (f.size / 1024).toFixed(1) + " KiB" }),
            el("td", null, dirty ? el("span", { class: "chip dirty", text: dirty.state }) : el("span", { class: "muted small", text: "committed" })));
        }))))
    ]);
  }

  // ---------- Source / commit viewer ----------
  var viewerText = null;
  function showViewer(title, meta) {
    $("viewer-title").textContent = title; $("viewer-meta").textContent = meta || "";
    var d = $("viewer");
    if (!d.open) { if (d.showModal) d.showModal(); else d.setAttribute("open", ""); }
  }
  function openSource(path) {
    viewerText = null;
    replace($("viewer-body"), el("p", { class: "muted", text: "Loading…" }));
    showViewer(path, "");
    fetch("/api/source?path=" + encodeURIComponent(path), { cache: "no-store" }).then(function (r) {
      return r.json().then(function (j) { if (!r.ok) throw new Error(j.error || ("HTTP " + r.status)); return j; });
    }).then(function (j) {
      viewerText = { path: j.path, text: j.text };
      $("viewer-meta").textContent = "Modified " + fmtTime(j.mtime) + " · " + j.size + " bytes" + (j.truncated ? " · TRUNCATED" : "") + " · read-only";
      drawViewer();
    }).catch(function (e) { replace($("viewer-body"), el("p", { class: "error", text: "Could not load source: " + e.message })); });
  }
  function drawViewer() {
    if (!viewerText) return;
    var raw = $("viewer-raw").checked || !/\.md$/.test(viewerText.path);
    var body = $("viewer-body");
    if (raw) replace(body, el("pre", { text: viewerText.text }));
    else replace(body, el("div", { class: "md" }, renderMarkdown(viewerText.text)));
  }
  function openCommit(hash) {
    viewerText = null;
    replace($("viewer-body"), el("p", { class: "muted", text: "Loading…" }));
    showViewer("Commit " + hash, "");
    fetch("/api/commit?hash=" + encodeURIComponent(hash), { cache: "no-store" }).then(function (r) { return r.json(); }).then(function (j) {
      if (!j.ok) throw new Error(j.error || "unavailable");
      $("viewer-meta").textContent = j.hash + " · " + j.author + " · " + fmtTime(j.commit_date);
      replace($("viewer-body"), [el("h3", { text: j.subject }), j.body ? el("pre", { text: j.body }) : null, el("h3", { text: "Files changed" }), el("pre", { text: j.stat || "(none)" })]);
    }).catch(function (e) { replace($("viewer-body"), el("p", { class: "error", text: "Could not load commit: " + e.message })); });
  }

  // Minimal Markdown → DOM (headings, fences, lists, paragraphs, inline code/bold/links). No HTML passthrough.
  function renderMarkdown(text) {
    var out = [], lines = String(text).split("\n"), i = 0, para = [], list = null;
    function flushPara() { if (para.length) { out.push(el("p", null, inline(para.join(" ")))); para = []; } }
    function flushList() { if (list) { out.push(list); list = null; } }
    while (i < lines.length) {
      var line = lines[i];
      if (/^\s*```/.test(line)) {
        flushPara(); flushList();
        var buf = []; i++;
        while (i < lines.length && !/^\s*```/.test(lines[i])) { buf.push(lines[i]); i++; }
        out.push(el("pre", { text: buf.join("\n") })); i++; continue;
      }
      var h = /^(#{1,6})\s+(.*)$/.exec(line);
      if (h) { flushPara(); flushList(); out.push(el("h" + Math.min(6, h[1].length + 1), null, inline(h[2]))); i++; continue; }
      var li = /^\s*(?:[-*]|\d+\.)\s+(.*)$/.exec(line);
      if (li) { flushPara(); if (!list) list = el("ul"); list.appendChild(el("li", null, inline(li[1]))); i++; continue; }
      if (/^\s*\|.*\|\s*$/.test(line)) { flushPara(); flushList(); var tb = []; while (i < lines.length && /^\s*\|/.test(lines[i])) { tb.push(lines[i]); i++; } out.push(el("pre", { text: tb.join("\n") })); continue; }
      if (!line.trim()) { flushPara(); flushList(); i++; continue; }
      if (list && /^\s{2,}\S/.test(line)) { list.lastChild.appendChild(document.createTextNode(" ")); append(list.lastChild, inline(line.trim())); i++; continue; }
      flushList(); para.push(line.trim()); i++;
    }
    flushPara(); flushList();
    return out;
  }
  function inline(t) {
    var nodes = [], re = /(`[^`]+`)|\*\*([^*]+)\*\*|\[([^\]]+)\]\(([^)\s]+)\)/g, last = 0, m;
    while ((m = re.exec(t))) {
      if (m.index > last) nodes.push(t.slice(last, m.index));
      if (m[1]) nodes.push(el("code", { text: m[1].slice(1, -1) }));
      else if (m[2]) nodes.push(el("strong", { text: m[2] }));
      else nodes.push(safeUrl(m[4]) ? extLink(m[4], m[3]) : m[3] + " (" + m[4] + ")");
      last = re.lastIndex;
    }
    if (last < t.length) nodes.push(t.slice(last));
    return nodes;
  }

  // ---------- Main view: answer, scale, controls ----------
  // The only numbers on the main view come from the estimator config (published reference rate and
  // work) and a curated, reviewed current_result. Research activity never changes them by itself.
  var ui = { gpusExp: null, hardware: null, multiplier: 1, customRate: "" };
  function cfg() { return (state.snap && state.snap.estimator) || {}; }
  function hwList() { return cfg().hardware || []; }
  function hwById(id) { return hwList().filter(function (h) { return h.id === id; })[0] || null; }
  function sup(n) { return el("sup", { text: String(n) }); }
  function sciNode(l10) {
    var t = window.Estimator.sci(l10, 3).split("e");
    return [t[0] + "×10", sup(Number(t[1]))];
  }
  function gpuWord(exp) { var n = Math.pow(10, exp); return (exp >= 3 ? window.Estimator.humanNumber(exp) : String(n)) + (n === 1 ? " GPU" : " GPUs"); }

  var RESEARCH_TEXT = {
    reported_none: "No verified improvement from this research — the estimate is unchanged.",
    reported_positive: "A possible improvement was reported but is not verified — the estimate is unchanged until it is.",
    conflicting: "Research reports disagree and have not been assessed — the estimate is unchanged.",
    unknown: "The research has not stated a result yet — the estimate is unchanged."
  };
  var RESEARCH_CLASS = { reported_none: "o-none", reported_positive: "o-positive", conflicting: "o-conflict", unknown: "o-unknown" };

  function renderMain(s) {
    var E = window.Estimator, c = cfg();
    if (ui.gpusExp == null) {
      ui.gpusExp = Math.round(Math.log10(c.default_gpus || 1e6));
      ui.hardware = c.reference_hardware || "rtx5090";
      $("gpus").value = String(ui.gpusExp);
    }
    var cmp = E.comparison(c, s.outcome);
    // Verdict: current best work, measured reference GPU, the default fleet size.
    var ref = hwById(c.reference_hardware || "rtx5090");
    var verdict = "Unknown";
    if (ref && ref.ops_per_sec > 0) {
      var v = E.estimate(cmp.currentLog2 * E.LOG10_2, c.default_gpus || 1e6, ref.ops_per_sec).log10Years;
      verdict = v >= 3 ? "No — still far out of reach" : v >= 0 ? "Only with an enormous effort" : "Yes — within reach";
    }
    $("verdict").textContent = verdict;
    var o = s.outcome || { status: "unknown" };
    $("research-line").className = "research-line " + (cmp.changed ? "o-changed" : (RESEARCH_CLASS[o.status] || "o-unknown"));
    $("research-text").textContent = cmp.changed ? "A reviewed research result changed the estimate (see below)." : (RESEARCH_TEXT[o.status] || RESEARCH_TEXT.unknown);
    renderControls();
    renderAnswer();
    renderCompare(s, cmp);
  }

  function renderControls() {
    var c = cfg(), hw = hwById(ui.hardware);
    replace($("hw"), hwList().map(function (h) {
      var on = h.id === ui.hardware;
      return el("button", { type: "button", role: "radio", "aria-checked": on ? "true" : "false", class: "seg-btn" + (on ? " on" : ""),
        onclick: function () { selectHardware(h.id); } }, h.id === "custom" ? "Custom" : h.label.replace(/^NVIDIA /, ""),
        h.benchmarked === false ? el("span", { class: "seg-note", text: "no benchmark" }) : null);
    }));
    var speed = $("speed");
    var isCustom = hw && hw.id === "custom";
    $("custom-wrap").hidden = !isCustom;
    speed.hidden = isCustom;
    if (!isCustom) {
      var opts = (hw && hw.benchmarked === false ? [null] : []).concat(c.speed_multipliers || [1, 10, 100, 1000]);
      replace(speed, opts.map(function (m) {
        var on = m === ui.multiplier;
        var label = m == null ? "Unknown" : m === 1 ? (hw && hw.benchmarked ? "Reported" : "1×") : m.toLocaleString("en-US") + "×";
        return el("button", { type: "button", role: "radio", "aria-checked": on ? "true" : "false", class: "seg-btn" + (on ? " on" : "") + (m != null && !(m === 1 && hw && hw.benchmarked) ? " assumed" : ""),
          title: m == null ? "No benchmark recorded — no estimate" : m === 1 && hw && hw.benchmarked ? "Published rate" : "What-if: " + m + "× the RTX 5090 reference rate",
          onclick: function () { ui.multiplier = m; renderControls(); renderAnswer(); } }, label);
      }));
      $("speed-label").textContent = hw && hw.benchmarked === false ? "Assumed speed vs. RTX 5090" : "Speed per GPU";
    } else {
      $("speed-label").textContent = "Speed per GPU";
    }
  }
  function selectHardware(id) {
    var hw = hwById(id);
    ui.hardware = id;
    ui.multiplier = hw && hw.benchmarked === false ? null : 1;
    renderControls(); renderAnswer();
  }

  function renderAnswer() {
    var E = window.Estimator, c = cfg(), cmp = E.comparison(c, state.snap && state.snap.outcome);
    var hw = hwById(ui.hardware);
    $("gpus-out").textContent = gpuWord(ui.gpusExp);
    var sc;
    try {
      sc = E.scenario(c, { hardware: ui.hardware, gpus: Math.pow(10, ui.gpusExp), multiplier: ui.multiplier,
        customRate: E.parseNumber($("custom-rate").value), log2Work: cmp.currentLog2 });
      $("custom-rate").removeAttribute("aria-invalid");
    } catch (e) { sc = { rate: { known: false, basis: "unknown", reason: e.message } }; }
    var r = sc.rate, hwName = hw ? (hw.id === "custom" ? "your GPU" : hw.label) : "GPU";
    replace($("answer-setup"), [el("strong", { text: gpuWord(ui.gpusExp) }), " (" + hwName + ")"]);
    var tag = $("basis-tag"), note = $("hw-note");
    if (!r.known) {
      $("big-time").textContent = "Unknown";
      $("big-time").className = "big-time unknown";
      replace($("big-sub"), hw && hw.id === "custom" ? "Enter a measured speed to calculate." : "No relevant " + hwName + " benchmark is recorded here. Choose an assumed speed to explore.");
      tag.className = "basis-tag t-unknown"; tag.textContent = hw && hw.id === "custom" ? "Waiting for your rate" : "Not benchmarked";
      if (hw && hw.id === "custom" && $("custom-rate").value.trim()) $("custom-rate").setAttribute("aria-invalid", "true");
    } else {
      var res = sc.result;
      $("big-time").textContent = E.humanYears(res.log10Years);
      $("big-time").className = "big-time";
      var ratio = res.log10Years - Math.log10(E.AGE_OF_UNIVERSE_YEARS);
      replace($("big-sub"), [sciNode(res.log10Years), " years",
        ratio >= 0 ? " · about " + E.humanNumber(ratio) + "× the age of the universe" : ""]);
      if (r.basis === "measured") { tag.className = "basis-tag t-measured"; tag.textContent = "Extrapolated from reported RTX 5090 speed"; }
      else if (r.basis === "custom") { tag.className = "basis-tag t-assumed"; tag.textContent = "Your rate: " + E.sci(Math.log10(r.rate), 3) + " steps/s per GPU"; }
      else { tag.className = "basis-tag t-assumed"; tag.textContent = "Assumed " + r.multiplier.toLocaleString("en-US") + "× RTX 5090 speed — " + (hw && hw.benchmarked === false ? "not a " + hw.label.replace(/^NVIDIA /, "") + " benchmark" : "what-if, not measured"); }
    }
    // One-line hardware note (secondary).
    var src = hw && hw.source ? extLink(hw.source.url, hw.source.label) : null;
    if (hw && hw.benchmarked === false) {
      replace(note, [r.known ? "What-if only. " : "", "No relevant " + hw.label.replace(/^NVIDIA /, "") + " benchmark found — AI specs (FLOPS) don't convert into this workload. ",
        hw.source ? extLink(hw.source.url, "NVIDIA specs") : null]);
    } else if (hw && hw.id === "custom") {
      replace(note, "Use a rate you measured for secp256k1 point-addition steps per GPU (e.g. 25e9).");
    } else if (hw) {
      replace(note, [r.basis === "measured" ? "Assumes ideal scaling of a related workload: 19.3 billion steps/s per GPU, " : "What-if: faster software or chips. Published rate is 19.3 billion steps/s, ", "from ", src, "."]);
    }
    renderScale(sc, cmp);
    renderWhatChanges(cmp);
  }

  // Logarithmic time scale (HTML, positioned with CSSOM — allowed by the CSP).
  function renderScale(sc, cmp) {
    var E = window.Estimator, box = $("scale");
    var s = sc.result ? sc.result.log10Years : null;
    var lo = -4, hi = 24;
    if (s != null) { lo = Math.min(lo, Math.floor((s - 2) / 4) * 4); hi = Math.max(hi, Math.ceil((s + 2) / 4) * 4); }
    lo = Math.max(lo, -12); hi = Math.min(hi, 80);
    function pct(v) { return 100 * (Math.min(hi, Math.max(lo, v)) - lo) / (hi - lo); }
    function pos(node, v) { var p = pct(v); node.style.left = p + "%"; if (p < 12) node.classList.add("edge-l"); else if (p > 88) node.classList.add("edge-r"); return node; }
    var parts = [el("div", { class: "track" })];
    for (var t = Math.ceil(lo / 4) * 4; t <= hi; t += 4) {
      parts.push(pos(el("div", { class: "tick" }, el("span", null, t === 0 ? "" : ["10", sup(t)])), t));
    }
    parts.push(pos(el("div", { class: "ref" }, el("span", { class: "pin" }), el("span", { class: "ref-label", text: "1 year" })), 0));
    var uni = Math.log10(E.AGE_OF_UNIVERSE_YEARS);
    parts.push(pos(el("div", { class: "ref" }, el("span", { class: "pin" }), el("span", { class: "ref-label", text: "Age of the universe" })), uni));
    if (s != null) {
      var fill = el("div", { class: "fill" }); fill.style.width = pct(s) + "%";
      parts.splice(1, 0, fill);
      parts.push(pos(el("div", { class: "you" + (sc.rate.basis === "measured" ? "" : " assumed") }, el("span", { class: "you-label", text: E.humanYears(s) }), el("span", { class: "you-dot" })), s));
    } else {
      parts.push(el("div", { class: "scale-unknown", text: "No estimate without a measured or assumed speed" }));
    }
    replace(box, parts);
    box.setAttribute("aria-label", "Logarithmic time scale from 10^" + lo + " to 10^" + hi + " years. " +
      (s != null ? "Selected scenario: " + E.humanYears(s) + "; " : "Selected scenario: unknown; ") + "age of the universe: 13.8 billion years.");
  }

  function renderWhatChanges(cmp) {
    var E = window.Estimator, c = cfg(), ref = hwById(c.reference_hardware || "rtx5090");
    var items = [el("li", null, el("span", { class: "wc-icon", "aria-hidden": "true", text: "∑" }),
      el("div", null, el("strong", { text: "A fundamentally faster method" }),
        el("p", { text: "Needing far fewer operations would shrink the time by huge factors. This is what the research is searching for" + (cmp.changed ? "." : " — nothing verified so far.") })))];
    if (ref && ref.ops_per_sec > 0) {
      var top = c.speed_multipliers ? Math.max.apply(null, c.speed_multipliers) : 1000;
      var g = Math.max.apply(null, c.gpu_presets || [1e9]);
      var r = E.estimate(cmp.currentLog2 * E.LOG10_2, g, ref.ops_per_sec * top);
      items.push(el("li", null, el("span", { class: "wc-icon", "aria-hidden": "true", text: "×" }),
        el("div", null, el("strong", { text: "More or faster hardware (H200, B200, …)" }),
          el("p", { text: "Only divides the time. Even " + E.humanNumber(Math.log10(g)) + " GPUs, each " + top.toLocaleString("en-US") + "× the reported RTX 5090 rate: " + E.humanYears(r.log10Years) + "." }))));
    }
    replace($("what-change"), items);
  }

  function renderCompare(s, cmp) {
    var E = window.Estimator, o = s.outcome || {};
    function row(label, l2, cls, note) {
      var bar = el("div", { class: "cmp-bar " + cls }); bar.style.width = Math.max(2, 100 * l2 / 256) + "%";
      return el("div", { class: "cmp-row" }, el("div", { class: "cmp-label" }, el("span", { text: label }), el("span", { class: "cmp-val" }, "2", sup(+l2.toFixed(1)), " operations")),
        el("div", { class: "cmp-track" }, bar), note ? el("div", { class: "cmp-note", text: note }) : null);
    }
    var head = cmp.changed
      ? el("p", { class: "cmp-head changed", text: E.humanNumber((cmp.baselineLog2 - cmp.currentLog2) * E.LOG10_2) + "× fewer operations (reviewed result)" })
      : el("p", { class: "cmp-head", text: "No change to the estimate" });
    // The literal source sentences live in the evidence drawer; the main view only links to them.
    var quote = el("p", { class: "cmp-quote" }, "Based on the research team's live status file",
      o.source_mtime ? " (updated " + ago(o.source_mtime) + ")" : "", " · ",
      el("button", { type: "button", class: "linkish small", onclick: function () { var d = $("evidence-all"); d.open = true; d.querySelectorAll("details.sub")[1].open = true; d.scrollIntoView({ behavior: "smooth" }); } }, "see the exact sentences"));
    replace($("compare"), [head,
      row("Best known method (published)", cmp.baselineLog2, "base"),
      row("Best verified result from this research", cmp.currentLog2, cmp.changed ? "cur changed" : "cur", cmp.changed ? null : (cmp.pendingClaim ? "A claim exists but is unverified, so it is not counted." : "Same as the published method.")),
      el("p", { class: "cmp-axis muted small", text: "Bar length: number of doublings of work (0–256). One more doubling = twice the time." }),
      quote]);
  }

  function renderEstimatorMeta(s) {
    var e = s.estimator || {};
    replace($("est-assumptions"), (e.assumptions || []).map(function (a) { return el("li", { text: a }); }).concat(
      e.rate_source ? [el("li", null, el("strong", { text: "Rate units: " }), e.rate_source.units || "")] : [],
      (e.hardware || []).filter(function (h) { return h.benchmarked === false; }).map(function (h) {
        return el("li", null, el("strong", { text: h.label + ": " }), h.basis || "not benchmarked", " ", h.source ? extLink(h.source.url, h.source.label) : null);
      }),
      [el("li", null, el("strong", { text: "Current research result: " }), e.current_result ? "curated entry present" : "none recorded — the current estimate equals the published reference. ", el("span", { class: "muted", text: e.current_result_note || "" }))]));
    replace($("est-sources"), ["Rate: ", e.rate_source ? extLink(e.rate_source.url, e.rate_source.label) : "—", " · Work: ", e.work_source ? extLink(e.work_source.url, e.work_source.label) : "—"]);
  }

  function initControls() {
    $("gpus").addEventListener("input", function () { ui.gpusExp = Number($("gpus").value); if (state.snap) renderAnswer(); });
    $("custom-rate").addEventListener("input", function () { if (state.snap) renderAnswer(); });
    $("controls").addEventListener("submit", function (e) { e.preventDefault(); });
  }

  // ---------- Boot ----------
  document.addEventListener("DOMContentLoaded", function () {
    $("viewer-close").addEventListener("click", function () { $("viewer").close(); });
    $("viewer-raw").addEventListener("change", drawViewer);
    $("viewer").addEventListener("click", function (e) { if (e.target === $("viewer")) $("viewer").close(); });
    $("f-search").addEventListener("input", function () { if (state.snap) renderFindings(state.snap); });
    $("f-hint").addEventListener("change", function () { if (state.snap) renderFindings(state.snap); });
    initControls();
    loadSnapshot();
    connect();
    setInterval(tick, 1000);
  });
})();
