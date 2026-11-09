# Network stop, r530

Final GET plan plans/get-g8.json, URL https://link.springer.com/article/10.1007/s11139-022-00660-7, followed an automatic
302 cookie redirect cycle. The guard raised PolicyError "Already attempted URL" before the repeated article request.
No body was obtained and sources/g8-s11139-022-00660-7.html does not exist.

- The guard process exited 1; that exit and its traceback are in get_g8.output.txt.
- DISCLOSURE: my wrapper script ended with sys.exit(0), so get_g8.receipt.json records runner exit 0 although the guard
  failed. The receipt exit is therefore NOT evidence of guard success. Use the printed "guard exit 1".
- The guard's unavailable-event logging is whatever guard-ledger.jsonl records; I did not edit or backfill it.
- This article's identity was never confirmed. It surfaced in search 1 and may or may not be the final Craig-Merca paper.
  Treat that whole identified article as unavailable to all new deliveries. No retry, cookie workaround or alternate
  delivery was attempted. No further network request of any kind was made after this event.
