"""Record I163 reading/binding evidence, never execute or copy ancestor programs."""
from pathlib import Path
import hashlib
import json

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
TAG = "i163_corrected_bfss_contribution_astra"
OUT = ROOT / "frontier/sources" / TAG
CORPUS = "frontier/sources/i14_spectral_width_novelty_r3/corpus/"
PREPRINTS = CORPUS + "preprints/"
OLD = "frontier/sources/i162_fixed_sector_bfss_focused_astra/"
EXT = "frontier/sources/i155_fixed_sector_bfss_counting/external/"
P = PREPRINTS + (
    "Positive-eigenvalues-of-the-relative-SU-2-BFSS-Hamiltonian-October-5-2026/"
    "build/positive-eigenvalues-relative-su2-bfss.tex")
THRESHOLD = PREPRINTS + (
    "The-unique-threshold-bound-state-of-the-SU-N-BFSS-model-September-24-2026/"
    "build/manuscript/sections/")
MAP = "frontier/sources/i114_quantum_information_discovery/search-domain.json"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def record(path):
    data = (ROOT / path).read_bytes()
    return {"path": path, "bytes": len(data), "sha256": sha(data)}


def write(name, obj):
    with (OUT / name).open("x", encoding="utf8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)
        f.write("\n")


def main():
    assert not (OUT / "seal.json").exists()
    baseline = json.loads((OUT / "immutable-baseline.json").read_text())
    for row in baseline:
        assert record(row["path"]) == row, row["path"]
    readings = []
    refs = {}

    def read(path, ranges, purpose, origin="I163 fresh reading"):
        data = (ROOT / path).read_bytes()
        text = data.decode("utf8")
        lines = text.split("\n")
        if ranges is None:
            ranges = [[1, len(lines)]]
        pieces = []
        for start, end in ranges:
            assert 1 <= start <= end <= len(lines)
            part = "\n".join(lines[start-1:end])
            pieces.append({
                "start": start, "end": end, "sha256": sha(part.encode("utf8")),
                "chars": len(part), "ending": part[-180:]})
        refs[path] = record(path)
        readings.append({
            "path": path, "file_sha256": sha(data), "lf_split_count": len(lines),
            "ranges": pieces, "origin": origin, "purpose": purpose,
            "convention": "1-based inclusive LF split/join, no added final LF",
            "semantic_scope": "Only the supplied ranges; hashes are not semantic proof"})

    # Aggregate receipts retain full coverage already read before compaction,
    # not the inherited I162/I155 authors' reading claims.
    before = "I163 fresh reading before conversation compaction, aggregate coverage"
    read(P, None, "Complete source including all used proofs and bibliography", before)
    for name in ["fnt", "halpern", "simon158", "simon159", "dfs"]:
        read(EXT + name + ".txt", None, "Complete retained primary text", before)
    arefeva = "frontier/sources/i153_many_body_spectral_discovery/external/arefeva"
    read(arefeva + ".txt", None, "Complete retained primary text", before)
    read(EXT + "weich.txt", [[1, 665]], "Setup and complete Weyl proof; later trace-formula material excluded", before)
    read(EXT + "kr.txt", [[1, 290], [1142, 1445]],
         "Compact-manifold hypotheses and Weyl theorem/proof; intervening machinery excluded", before)
    read(EXT + "luscher.txt", [[1, 205], [553, 614], [1200, 1274]],
         "Model setup, spectral statement and complete confinement Appendix D",
         "I163 fresh reading across pre- and post-compaction turns")
    for name in ["01-introduction.tex", "02-algebra.tex", "04-fast-analysis.tex", "07-counting.tex"]:
        read(THRESHOLD + name, None, "Complete named companion section; other sections not claimed read")
    read(PREPRINTS + "Uniform-excess-charge-for-Coulomb-molecules-and-the-outer-radius-of-neutral-atoms-September-24-2026/build/sections/03-localization.tex",
         None, "Complete localization and Neumann cube comparison operations")
    read(PREPRINTS + "A-Coulomb-Ground-State-Density-without-Kohn-Sham-Ensemble-Representation-September-25-2026/build/sections/03-angle-spectrum.tex",
         [[1, 300], [301, 764]], "Complete angle/weighted gap section")
    read(PREPRINTS + "Universal-optimality-of-the-triangular-lattice-September-23-2026/build/sections/08-arithmetic-verification.tex",
         [[813, 949]], "Includes complete local weighted cell operation at 881–945, not entire paper")
    matrix = PREPRINTS + "Sharp-one-dimensional-Lieb-Thirring-inequalities-for-matrix-potentials-October-5-2026/build/sections/"
    read(matrix + "introduction.tex", None, "Actual theorem scope")
    read(matrix + "spectral.tex", None, "Complete spectral passage; action/trace machinery unused")
    read(OLD + "i155-brief.txt", [[1, 150], [151, 300], [301, 490], [491, 662]],
         "All decoded brief text, including embedded report, repeated stdout and finalized response")
    read(OLD + "i158-brief.txt", [[1, 150], [151, 300], [301, 470], [471, 769]],
         "All decoded brief text, including report and finalized response")
    for name in ["i155-other-fields.json", "i158-other-fields.json"]:
        read(OLD + name, None, "All remaining top-level original fields")
    for path in [
        "frontier/reviews/i162-fixed-sector-bfss-focused-astra.md",
        "frontier/iterations/i162-bfss-normalization-parent-correction.md",
        "frontier/iterations/iteration163-corrected-bfss-contribution-factory-astra-task.json",
        "AGENTS.md", "sources/upstream.json"]:
        read(path, None, "Complete context/source-contract reading")
    read("frontier/iterations/i155-fixed-sector-bfss-counting.md", None,
         "Complete original report; exact failure retained", before)

    bindings = []
    bind_path = "frontier/sources/i155_fixed_sector_bfss_counting/new-bindings.json"
    refs[bind_path] = record(bind_path)
    for pair in json.loads((ROOT / bind_path).read_text()):
        if Path(pair["text"]["path"]).stem not in [
                "dfs", "simon158", "simon159", "kr", "fnt", "luscher", "weich", "halpern"]:
            continue
        for role in ["pdf", "text"]:
            assert record(pair[role]["path"]) == pair[role]
            refs[pair[role]["path"]] = pair[role]
        bindings.append({"pdf": pair["pdf"], "text": pair["text"],
                         "url": pair["url"], "mode": "Inherited PDF/text pair; no extraction rerun"})
    a_path = "frontier/sources/i153_many_body_spectral_discovery/new-bindings.json"
    refs[a_path] = record(a_path)
    a = next(x for x in json.loads((ROOT / a_path).read_text())
             if x["text_binding"]["path"] == arefeva + ".txt")
    for role in ["source_binding", "text_binding"]:
        assert record(a[role]["path"]) == a[role]
        refs[a[role]["path"]] = a[role]
    bindings.append({"pdf": a["source_binding"], "text": a["text_binding"],
                     "url": a["log"]["url"], "version": "hep-th/9911149v1",
                     "mode": "Inherited PDF/text pair; no extraction rerun"})
    p_binding = json.loads((ROOT / (OLD + "source-bindings.json")).read_text())["P"]
    for role in ["pdf", "text", "tex"]:
        refs[p_binding[role]["path"]] = p_binding[role]
    bindings.append({"pdf": p_binding["pdf"], "text": p_binding["text"], "tex": p_binding["tex"],
                     "mode": "Pinned binding reused; TeX controls coefficient; no new PDF semantic claim"})
    domain = json.loads((ROOT / MAP).read_text())
    lookup = {row["local"]: row for row in domain if row["kind"] != "outside_bytes"}
    pinned = []
    for path in sorted(refs):
        if path.startswith(CORPUS):
            row = lookup[path]
            pinned.append({"local": path, "path": row["path"],
                           "git_sha": row["git_sha"],
                           "sha256": row["sha256"],
                           "url": "https://raw.githubusercontent.com/openai/math/"
                                  "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/" + row["path"]})

    task_views = []
    for n, suffix in [(155, "fixed-sector-bfss-counting"),
                      (158, "fixed-sector-bfss-counting-r2")]:
        task_path = f"frontier/iterations/iteration{n}-{suffix}-task.json"
        task = json.loads((ROOT / task_path).read_text())
        brief = OLD + f"i{n}-brief.txt"
        fields = OLD + f"i{n}-other-fields.json"
        assert (ROOT / brief).read_text() == task["brief"]
        assert json.loads((ROOT / fields).read_text()) == {k: v for k, v in task.items() if k != "brief"}
        task_views.append({"task": task_path, "brief": brief, "other_fields": fields,
                           "characters": len(task["brief"])})

    # Immutable excerpts, not snapshots of giant mutable ledgers or I161 work.
    ledgers = []
    for path, start, end in [
        ("frontier/iterations/README.md", 1, 31),
        ("frontier/TEN-FINDINGS.md", 1, 34),
        ("frontier/README.md", 24, 36)]:
        text = (ROOT / path).read_text()
        excerpt = "\n".join(text.split("\n")[start-1:end])
        ledgers.append({"path": path, "observed": record(path), "start": start, "end": end,
                        "text": excerpt, "excerpt_sha256": sha(excerpt.encode()),
                        "scope": "Live file may drift; excerpt itself immutable. No active I161 binding."})
    write("reading.json", readings)
    write("references.json", sorted(refs.values(), key=lambda x: x["path"]))
    write("bindings.json", bindings)
    write("pinned-passages.json", pinned)
    write("task-views.json", task_views)
    write("ledger-excerpts.json", ledgers)
    print(json.dumps({"status": "RECORDED", "readings": len(readings),
                      "references": len(refs), "bindings": len(bindings),
                      "pinned_passages": len(pinned)}, indent=2))


if __name__ == "__main__":
    main()
