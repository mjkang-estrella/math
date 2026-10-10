#!/usr/bin/env python3
"""Preparation only. Writes only I98 evidence. Not invoked by final verification."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import json
import hashlib
import subprocess
import re
import html

ROOT = Path(__file__).resolve().parents[3]
S = ROOT / "frontier/sources/i98_complex_kahler_discovery"
E = ROOT / "frontier/experiments/i98_complex_kahler_discovery"

def sha(b):
    return hashlib.sha256(b).hexdigest()

def put(p, value):
    p.write_text(json.dumps(value, ensure_ascii=False, indent=2)+"\n")

def rel(p):
    return str(p.relative_to(ROOT))

def main():
    inherited = ROOT/"frontier/sources/i88_nonlinear_banach_discovery/search-domain.json"
    domain = json.loads(inherited.read_bytes())
    put(S/"search-domain.json", domain)
    refs = [{"path":rel(inherited), "sha256":sha(inherited.read_bytes())}]
    put(S/"immutable-references.json", refs)
    inputs = []
    drift = {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
             "frontier/iterations/README.md"}
    for p in sorted((S/"snapshots").rglob("*")):
        if p.is_file():
            original = str(p.relative_to(S/"snapshots"))
            inputs.append({"original":original, "snapshot":rel(p),
                           "may_drift":original in drift,
                           "sha256":sha(p.read_bytes())})
    put(S/"inputs.json", inputs)
    corpus = "frontier/sources/i14_spectral_width_novelty_r3/corpus"
    cmd = ["rg", "--files", "--no-ignore", corpus]
    found = sorted(subprocess.check_output(cmd, cwd=ROOT).decode().splitlines())
    put(S/"i14-files.json", {"command":cmd, "files":found})
    tree = json.loads((S/"snapshots/sources/preprints-tree.json").read_bytes())
    titles = sorted({x["path"].split("/")[1] for x in tree["tree"]
                     if len(x["path"].split("/"))>2})
    put(S/"all-titles.json", titles)
    selected = json.loads((S/"selected-inventory.json").read_bytes())
    bypath = {x["path"]:x for x in domain}
    read = []

    def passage(path, start, end, label, scope):
        p = ROOT/path
        raw = p.read_bytes()
        t = raw.decode(errors="replace")
        lines = t.split("\n")
        end = min(end or len(lines), len(lines))
        excerpt = "\n".join(lines[start-1:end])
        item = {"local":path, "label":label, "scope":scope,
                "line_convention":"LF split; formfeeds remain within a line",
                "start":start, "end":end, "total_LF_lines":len(lines),
                "total_LF_newlines":raw.count(b"\n"),
                "total_splitlines":len(t.splitlines()),
                "sha256":sha(raw), "passage_sha256":sha(excerpt.encode()),
                "passage":excerpt}
        row = next((x for x in domain if x["local"]==path), None)
        if row:
            item["upstream_path"] = row["path"]
            item["url"] = "https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/"+row["path"]
            item["git_sha"] = row["git_sha"]
        read.append(item)

    k3 = "preprints/Every-complex-K3-surface-is-Oka-September-23-2026/build/sections/"
    for tail,a,z,label in [
        ("introduction.tex",1,116,"K3 exact main theorem and stronger consequences"),
        ("local.tex",1,66,"fixed-target L and complete-strip criterion"),
        ("local.tex",293,397,"complete Stein chart/deformation/gluing operations"),
        ("local.tex",398,None,"complete planar propagation proof through ending"),
        ("projective.tex",1,None,"complete projective genus-one/flow construction"),
        ("dense.tex",1,None,"complete interpolation and projective-spray consequences"),
        ("dynamics.tex",1,None,"complete individual-period transfer and theorem ending"),
        ("degeneration.tex",1,130,"unrestricted-open-region statement and model"),
        ("degeneration.tex",445,None,"finite raw atlas deformation through proof ending"),
        ("globalization.tex",1,175,"passive parameters and full complexification proof")]:
        passage(bypath[k3+tail]["local"],a,z,label,"read proof unit/statement as specified")
    units = [
        ("A-surface-counterexample-to-Shafarevich-holomorphic-convexity-September-23-2026/build/sections/06-surface.tex",1,None,"complete actual surface/fiber topology"),
        ("Semialgebraic-universal-covers-of-normal-projective-varieties-September-24-2026/build/main.tex",290,327,"complete existing Remmert corollary proof"),
        ("The-abelianity-conjecture-for-special-compact-Kahler-manifolds-September-23-2026/build/sections/introduction.tex",170,235,"complete compactifiable-cover corollary proof"),
        ("Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/build/intro.tex",1,140,"exact compatible splitting and stronger projective scope"),
        ("Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/build/05_symmetry.tex",1,None,"complete final bounded-realization and symmetry step"),
        ("Conditional-good-minimal-models-for-compact-Kahler-fourfolds-October-6-2026/build/sections/introduction.tex",1,92,"conditional revised good-model statement"),
        ("Log-abundance-for-compact-Kahler-spaces-under-logarithmic-Iitaka-subadditivity-October-6-2026/build/sections/01-introduction.tex",30,78,"exact log-Iitaka hypothesis and conditional theorem")]
    for tail,a,z,label in units:
        passage(bypath["preprints/"+tail]["local"],a,z,label,"screen/read unit; no upstream audit")
    for name,a,z,label in [
        ("larusson-2011.pdf.txt",1,None,"complete primary paper including finite uniformity and family gap"),
        ("kusakabe-2020.pdf.txt",1,180,"exact POPAI/convex ellipticity/local sprays"),
        ("kusakabe-2020.pdf.txt",459,547,"complete fixed-target CAP recentering proof and equivalences"),
        ("kusakabe-2020.pdf.txt",683,700,"localization criterion statement"),
        ("xie-zhao-v2.pdf.txt",1,290,"complete vertical integration/symplectic/volume spray proofs"),
        ("xie-zhao-v2.pdf.txt",430,574,"complete preserved-pencil deformation through ending"),
        ("kusakabe-matsumura.pdf.txt",1,150,"exact current compact Kähler obstruction statements"),
        ("kusakabe-matsumura.pdf.txt",485,904,"complete Examples 2.9/2.10 obstruction proofs and consequence")]:
        passage(rel(S/"external"/name),a,z,label,"primary literature proof/statement reading, not independent audit")
    put(S/"read-manifest.json", read)

    history = {}
    rx = re.compile(r"Oka|Kähler|Kahler|Kuga|Hodge|nonconical|I9[0-8]|substantial|publication",re.I)
    for p in sorted(drift):
        lines = (S/"snapshots"/p).read_text().splitlines()
        history[p] = [{"splitline":i+1,"text":v} for i,v in enumerate(lines) if rx.search(v)]
    put(S/"history-screen.json", {"expression":rx.pattern,"convention":"splitlines","hits":history})

    requests = []
    for p in sorted((S/"external").glob("*requests.json")):
        for x in json.loads(p.read_bytes()):
            row = dict(x)
            f = S/"external"/x["file"]
            row["local"] = rel(f)
            row["sha256"] = sha(f.read_bytes())
            if f.suffix==".pdf" and f.read_bytes().startswith(b"%PDF"):
                t = Path(str(f)+".txt")
                row["text"] = rel(t)
                row["text_sha256"] = sha(t.read_bytes())
            requests.append(row)
    put(S/"primary-manifest.json", requests)
    versions = []
    for p in sorted((S/"external").glob("*abs.html")):
        t=p.read_text()
        title=re.search(r"<title>(.*?)</title>",t,re.S)
        start=t.find('class="submission-history"')
        if start<0: start=t.find("submission-history")
        end=t.find('class="extra-services"',start)
        if end<0: end=start+2500
        raw=t[start:end]
        versions.append({"local":rel(p),"title":html.unescape(title.group(1)) if title else None,
                         "sha256":sha(p.read_bytes()),
                         "history_html":raw,
                         "history_text":html.unescape(re.sub("<[^>]*>"," ",raw))})
    put(S/"versions.json", versions)
    pinpdfs = []
    for lead in ["Every-complex-K3-surface-is-Oka","Semialgebraic-universal-covers",
                 "A-surface-counterexample-to-Shafarevich"]:
        row=next(x for x in domain if lead in x["path"] and x["kind"]=="outside_pdf")
        pinpdfs.append(row)
    put(S/"pdf-replays.json",pinpdfs)
    out=subprocess.check_output([sys.executable,"-B",rel(E/"diagnostics.py")],cwd=ROOT)
    (E/"diagnostic-results.json").write_bytes(out)
    put(S/"preseal-events.json", [
        {"status":"retained preparation failure","event":"One web orchestration call had SyntaxError: Unexpected string from a malformed query literal; it made no web request. Corrected query call completed."},
        {"status":"retained preparation failure","event":"Metadata parser import failed: ModuleNotFoundError: No module named 'bs4'. Standard-library re/html parser was used instead; no package installation."},
        {"status":"retained extraction warning","event":"pdftotext for Kusakabe–Matsumura and Xie–Zhao printed 'Syntax Warning: Mismatch between font type and embedded font file'; returned exit 0 and produced retained text. Warnings were not interpreted as mathematical failures."},
        {"status":"scope limitation","event":"Some initial combined tool outputs were truncated. Read-manifest records only stated inspected units; subsequent focused reads included every proof ending used in A98/W98."}
    ])
    print(json.dumps({"status":"prepared","read_records":len(read),
                      "corpus_files":len(found),"primary_responses":len(requests)}))

if __name__=="__main__":
    main()
