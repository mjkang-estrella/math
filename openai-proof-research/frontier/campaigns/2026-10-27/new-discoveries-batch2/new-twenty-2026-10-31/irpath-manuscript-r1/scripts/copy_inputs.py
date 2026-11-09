"""Copy the frozen inputs used by the dossier into the lane, byte for byte, and record a receipt.

Usage (from the lane directory): python3 -I scripts/copy_inputs.py receipts/copy-receipt.json
Never overwrites an existing destination file.  Reads only the listed source files.
"""
import sys
sys.dont_write_bytecode = True
import hashlib, json, os, datetime

LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CAMP = os.path.dirname(LANE)
EC = "expanded-corpus-r209"
RV = "irpath-review-r1"
FM = "irpath-formal-r1"
PF = "irpath-parent-final-r1"
S1812 = EC + "/sources/src-1812.03382-20261105T100524638204"
S2104 = EC + "/sources/src-2104.09004-20261105T095514741031"
S2003 = EC + "/sources/src-2003.05956-20261105T102704496621"
D = RV + "/downloads/"
R = RV + "/receipts/"

COPIES = [
    # MathDB raw line
    (EC + "/raw/350452.jsonl", "mathdb-350452.jsonl"),
    (EC + "/raw/350452.jsonl", "inputs/mathdb/350452.jsonl"),
    # primary sources: arXiv e-print archives (gzip tar) as fetched, receipts, main TeX files
    (S1812 + "/body", "inputs/sources/arXiv-1812.03382v3.tar.gz"),
    (S1812 + "/receipt.json", "inputs/sources/arXiv-1812.03382v3.receipt.json"),
    (S1812 + "/extracted/Irredundance_Graphs.tex", "inputs/sources/1812.03382v3/Irredundance_Graphs.tex"),
    (S2104 + "/body", "inputs/sources/arXiv-2104.09004v2.tar.gz"),
    (S2104 + "/receipt.json", "inputs/sources/arXiv-2104.09004v2.receipt.json"),
    (S2104 + "/extracted/Irredundance_Trees_May2020.tex", "inputs/sources/2104.09004v2/Irredundance_Trees_May2020.tex"),
    (S2003 + "/body", "inputs/sources/arXiv-2003.05956v1.tar.gz"),
    (S2003 + "/receipt.json", "inputs/sources/arXiv-2003.05956v1.receipt.json"),
    (S2003 + "/extracted/Reconfig_March2020.tex", "inputs/sources/2003.05956v1/Reconfig_March2020.tex"),
    (D + "eprint-1812.03382v1-20261105T110126174530Z/body", "inputs/sources/arXiv-1812.03382v1.tar.gz"),
    (R + "eprint-1812.03382v1-20261105T110126174530Z.json", "inputs/sources/arXiv-1812.03382v1.receipt.json"),
    (D + "eprint-1812.03382v2-20261105T110130747896Z/body", "inputs/sources/arXiv-1812.03382v2.tar.gz"),
    (R + "eprint-1812.03382v2-20261105T110130747896Z.json", "inputs/sources/arXiv-1812.03382v2.receipt.json"),
    (D + "eprint-2104.09004v1-20261105T110233245912Z/body", "inputs/sources/arXiv-2104.09004v1.tar.gz"),
    (R + "eprint-2104.09004v1-20261105T110233245912Z.json", "inputs/sources/arXiv-2104.09004v1.receipt.json"),
    (EC + "/sources/abs-1812.03382-20261105T095725683008/body", "inputs/sources/abs-1812.03382.html"),
    (EC + "/sources/abs-1812.03382-20261105T095725683008/receipt.json", "inputs/sources/abs-1812.03382.receipt.json"),
    (EC + "/sources/abs-2104.09004-20261105T095430713741/body", "inputs/sources/abs-2104.09004.html"),
    (EC + "/sources/abs-2104.09004-20261105T095430713741/receipt.json", "inputs/sources/abs-2104.09004.receipt.json"),
    (D + "abs-2003.05956-20261105T110243383648Z/body", "inputs/sources/abs-2003.05956.html"),
    (R + "abs-2003.05956-20261105T110243383648Z.json", "inputs/sources/abs-2003.05956.receipt.json"),
    (D + "openalex-title-irredundance-20261105T110308148237Z/body", "inputs/sources/openalex-title-irredundance.json"),
    (R + "openalex-title-irredundance-20261105T110308148237Z.json", "inputs/sources/openalex-title-irredundance.receipt.json"),
    (D + "openalex-citing-3-20261105T110321417952Z/body", "inputs/sources/openalex-citing-3.json"),
    (R + "openalex-citing-3-20261105T110321417952Z.json", "inputs/sources/openalex-citing-3.receipt.json"),
    # discovery lane
    (EC + "/CANDIDATE.md", "inputs/discovery/CANDIDATE.md"),
    (EC + "/SUMMARY.md", "inputs/discovery/SUMMARY.md"),
    (EC + "/results.json", "inputs/discovery/results.json"),
    (EC + "/outputs/certificate-350452.json", "inputs/discovery/certificate-350452.json"),
    (EC + "/outputs/irgraph-N7.txt", "inputs/discovery/irgraph-N7.txt"),
    (EC + "/outputs/irgraph-N8.txt", "inputs/discovery/irgraph-N8.txt"),
    (EC + "/outputs/irgraph-N9-chunks.jsonl", "inputs/discovery/irgraph-N9-chunks.jsonl"),
    (EC + "/outputs/registry-screen.json", "inputs/discovery/registry-screen.json"),
    (EC + "/scripts/certificate_350452.py", "inputs/discovery/scripts-as-text/certificate_350452.py.txt"),
    (EC + "/scripts/irgraph.py", "inputs/discovery/scripts-as-text/irgraph.py.txt"),
    (EC + "/scripts/irgraph_chunk.py", "inputs/discovery/scripts-as-text/irgraph_chunk.py.txt"),
    # independent review
    (RV + "/REVIEW.md", "inputs/review/REVIEW.md"),
    (RV + "/review.json", "inputs/review/review.json"),
    (RV + "/logs/check_G.log", "inputs/review/logs/check_G.log"),
    (RV + "/logs/audit_cert.log", "inputs/review/logs/audit_cert.log"),
    (RV + "/logs/hits9.log", "inputs/review/logs/hits9.log"),
    (RV + "/logs/source_lemmas.log", "inputs/review/logs/source_lemmas.log"),
    (RV + "/logs/search-upto7.json", "inputs/review/logs/search-upto7.json"),
    (RV + "/logs/search-upto8.json", "inputs/review/logs/search-upto8.json"),
    # root
    ("irpath-root-ruling-r1.json", "inputs/root/irpath-root-ruling-r1.json"),
    ("irpath-root-check-r1/check.py", "inputs/root/check.py.txt"),
    ("irpath-root-check-r1/check-output.json", "inputs/root/check-output.json"),
    (PF + "/replay-result.json", "inputs/root/replay-result.json"),
    (PF + "/registry-refresh.json", "inputs/root/registry-refresh.json"),
    (PF + "/root-replay.out", "inputs/root/root-replay.out"),
    (PF + "/logs/root-meta.log", "inputs/root/root-meta.log"),
    # formal lane documents and logs (the packet itself is lean/source.zip)
    (FM + "/source.zip", "lean/source.zip"),
    (FM + "/SUMMARY.md", "inputs/formal/SUMMARY.md"),
    (FM + "/PROOF.md", "inputs/formal/PROOF.md"),
    (FM + "/STATEMENT-CORRESPONDENCE.md", "inputs/formal/STATEMENT-CORRESPONDENCE.md"),
    (FM + "/REPRODUCE.md", "inputs/formal/REPRODUCE.md"),
    (FM + "/results.json", "inputs/formal/results.json"),
    (FM + "/module-order.txt", "inputs/formal/module-order.txt"),
    (FM + "/logs/source-scan.json", "inputs/formal/logs/source-scan.json"),
]
for m in ["General", "GData", "Four", "Three", "Finite", "Endpoint", "Control", "Audit"]:
    for kind in ["compile", "checker"]:
        COPIES.append((FM + "/final-extraction/logs/%s.%s.log" % (m, kind),
                       "inputs/formal/final-extraction-logs/%s.%s.log" % (m, kind)))


def sha(p):
    with open(p, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def main():
    rec = []
    for src, dst in COPIES:
        s = os.path.join(CAMP, src)
        d = os.path.join(LANE, dst)
        os.makedirs(os.path.dirname(d), exist_ok=True)
        with open(s, "rb") as f:
            data = f.read()
        with open(d, "xb") as f:
            f.write(data)
        hs, hd = sha(s), sha(d)
        assert hs == hd
        rec.append({"source": src, "dest": dst, "sha256": hd, "bytes": len(data)})
    out = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "campaign_dir": CAMP,
           "n": len(rec), "all_identical": True, "copies": rec}
    with open(sys.argv[1], "x") as f:
        json.dump(out, f, indent=1)
    print(json.dumps({"n": len(rec), "lean/source.zip": sha(os.path.join(LANE, "lean/source.zip"))}))


if __name__ == "__main__":
    main()
