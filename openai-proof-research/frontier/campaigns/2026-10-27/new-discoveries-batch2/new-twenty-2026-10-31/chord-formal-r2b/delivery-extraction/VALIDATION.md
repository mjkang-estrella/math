# Validation receipt — Round 2B

All 109 mathematical modules passed a fresh extracted strict serial rebuild and explicit-module leanchecker. The audit module also compiled and passed explicit-module leanchecker. Every call used the resource wrapper. No frozen source changed.

CLOSURE inventory=219366 audited=219366 LOCAL=6478; sets equal

LOCAL declarations: 6478. Forbidden LOCAL metadata and unapproved transitive axioms: zero. Upstream metadata is reported separately in results.json. The audit reads opaque values and generated declarations and checks exact inventory/audited set equality. Its complete rows are in fresh-extraction/audit.jsonl.

Independent regression checked 995,572 diagram/assignment pairs through n = 5 with zero boundary-model mismatches. All four negative controls passed. A separate Lean negative control refutes uniqueness at n = 4.

The final delivery archive updates only packaging scripts and report metadata relative to the replay archive. Every delivered Lean file is byte-identical to its freshly rebuilt source; final extraction equality is checked by scripts/finalize.py. No object files or build markers are included in the source archive.

Peak sampled RSS over development and replay: 2972496 KiB. CPU 120 s, wall 140 s, RSS 6 GiB, taskset CPUs 0 and 1, MALLOC_ARENA_MAX=2 and Lean -M3500 remained in force. Bounded failed development attempts are retained in logs; successful replay is in fresh-extraction/replay.log.

The closed Props are FiveChordLemma and FourChordEnumeration. General existence, bipartite planarity, triangle reduction and large-n rigidity remain unproved. This receipt is not acceptance. Root decides.
