# Resource and process accounting

The first actual shell command was exactly the requested timeout 20 python3 -I -B .../expanded-corpus-r333/bootstrap.py. It returned exit 0. Its original bootstrap-receipt.json was neither overwritten nor used as a later job's receipt.

Every subsequent shell job was timeout 140 python3 -I -B, with the Python process setting sched affinity to the first at most two CPUs of its already-allowed affinity mask, CPU soft/hard 120 seconds, and address-space soft/hard 6 GiB before source reads. Public GET fetching used at most two threads in the same capped Python process. No mathematical program was executed. No subprocesses were launched by the Python source processors. Shell timeout wrappers and managed services have no group/cgroup RSS measurement here.

resource-jobs.jsonl contains actual self resource.getrusage high-water/resource values for the fetch batches and later explicitly logged source-processing jobs. These are SELF values, not process-group or cgroup RSS. Earlier jobs printed resource values into tool outputs where noted, but were not all logged contemporaneously to disk. Peak group RSS and continuous sampled RSS are unavailable. Affinity/AS limits are controls, not evidence of group memory sampling. Do not infer full telemetry compliance from managed tool elapsed times.

Known exception: the first HTML text conversion attempted to import bs4; this failed immediately with ModuleNotFoundError and exit 1, before source-file reads. The next job used Python's standard-library HTMLParser and exited 0. No package/dependency changes were made. Several broad source-context outputs were truncated by the tool, and the priority definition/proof passages were reread with bounded targeted output. Bodies never reread are not promoted to proof review.

The source/allowlist probe and initial provenance extraction exited 0; exact allowlist scan, parser replacement, source-context processing, definition reads, version comparison, source metadata reconciliation, history family reads and assembly exited 0. Their precise tool output wall times are service reports, not independently sampled process-group usage. The original parser failure is the only known local nonzero exit. No timeouts or unhandled worker failures occurred.

Asynchronous exec sessions 63242, 91992, 85071 and 12663 each received completion with exit 0. (There were four such sessions; SUMMARY's generic session count is corrected by this explicit inventory.) All HTTP worker futures were awaited through ThreadPoolExecutor context shutdown. No outstanding sessions or background local jobs remain.

HTTP receipts count saved response-body bytes. For HTTP errors no error body was read; a recorded bytes=0 means zero saved/read body bytes, not proof that the server transmitted no bytes. HTTPS verification was kept enabled. No denied route was retried.

Web search/PDF extraction services are managed external services: local CPU affinity, CPU time, AS and RSS are unavailable for them. They were used only for public read-only search/GET extraction; no full-compliance inference is made. Their extracted PDF mathematical symbols can be mistranscribed; primary HTML controls the exchange and rigidity definitions where available. No screenshot/visual-figure clearance is claimed.

