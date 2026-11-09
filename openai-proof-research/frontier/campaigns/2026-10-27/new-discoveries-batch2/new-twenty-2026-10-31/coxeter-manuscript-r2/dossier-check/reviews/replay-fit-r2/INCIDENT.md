# Boundary violation in first diagnostic

Before running the copied round 1 durable-profile source, I failed to rewrite its absolute marker-log path. The canceled run appended exactly these three lines to replay-fit-r1/logs/330264-declarations.log:

    ENTER AP 27209878
    ENTER AQ 27210402
    ENTER A_pq 27211093

I stopped the process after detecting the path, after 19 seconds (raw wait status 15), and corrected the copied source to write in replay-fit-r2. The corrected diagnostic then ran under the original caps and reached wall 140 seconds. The old log was not restored because that would require a further unauthorized write outside the lane. This violated the write-only-in-round-2 instruction. No mathematical source or build object outside the assigned lane was modified. Root should account for this incident separately from the technical replay evidence.
