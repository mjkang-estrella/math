# PROVENANCE-ADDENDUM — canonical literal bindings and write-failure trail

Companion to ACTUALBRIEF.md. This file records the authoritative provenance artifact and the exact, retained failures that occurred while authoring it. Nothing here changes the scientific disposition: zero qualified survivors.

## Canonical artifact
`literal-bindings.json`
- sha256 74541d317bdd03528e2fdb5f5c866d4176c358ad0cb1c89807264a548c9b24b5
- 43829 bytes, valid JSON, count 20, ids in reservation order (verified equal to reservation.json ids), all statements non-empty, minimum decoded statement length 581 characters, titles present for all twenty, twelve distinct corpus chunks (0002,0003,0004,0005,0007,0008,0009,0010,0011,0012,0013,0014).
- Corpus root recorded in the file: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/pi-mathdb-full-corpus-inventory-r301/corpus
- Per binding: chunk path, chunk sha256, one-based line, raw-line length and sha256, trailing-newline flag, statement-token sha256, decoded-statement length and sha256, title, status, source_url, source_name, first_stated_year, solution_count, tags, and the complete decoded statement.
- Hash definitions are embedded in the file: raw_line = bytes of the JSONL line excluding its trailing newline; statement_token = json.dumps(statement, ensure_ascii=False, separators=(',',':')); decoded_statement = the statement string encoded UTF-8.

## Retained failures (all receipts preserved; no unchanged failed rerun)
1. `emit-literal-bindings` — exit 1. My corpus root was wrong (I used /home/mj-kang/Documents/Dev/math/openai-proof-research/lanes/... instead of .../frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/...), so open() raised FileNotFoundError; zero bytes of stdout and a zero-byte .output.txt. This was diagnosed from the receipt, not by rerunning it. The correct root was then recovered from the command recorded in the retained `corpus-locate-20.receipt.json` (inspected under `inspect-locate-receipt-1`).
2. The first `write_lane.py literal-bindings.json` received empty stdin (because the failed emit produced no output) and wrote a 0-byte file. Disclosed; the file was subsequently overwritten by the corrected authoring step, so no 0-byte artifact remains, but the receipt trail shows the empty write.
3. `check-bindings-1` — exit 1, JSONDecodeError "Expecting value: line 1 column 1" against the 0-byte file. Retained; not rerun unchanged.
4. `emit-literal-bindings-r2` — exit 0, but my extraction pipeline used `sed -n '/BEGIN/,/END/p' | sed '1d;$d'`. `$d` deletes the last line of the whole stream (the run receipt), not the END marker, so the literal `<<<END-BINDINGS>>>` line was written into literal-bindings.json. Diagnosis under `inspect-bindings-tail-1` (the file ended with "}\n<<<END-BINDINGS>>>\n").
5. `check-bindings-2` — exit 1, JSONDecodeError "Extra data: line 488 column 1", caused by (4). Retained.
6. `emit-literal-bindings-r3` + `awk '/^\{"utc":/{exit} {print}'` — the corrected extraction stops at the run receipt line, so only the pretty-printed JSON is written. `check-bindings-3` then parsed the file successfully (count 20, all fields present, sha256 as above); `check-bindings-4` verified ids_match True against reservation.json ids.
7. The earlier direct write of `literal-scan-raw.json` from inside `corpus-locate-20` remains disclosed in ACTUALBRIEF.md §7; it is retained as a non-canonical intermediate and is not the provenance record.
