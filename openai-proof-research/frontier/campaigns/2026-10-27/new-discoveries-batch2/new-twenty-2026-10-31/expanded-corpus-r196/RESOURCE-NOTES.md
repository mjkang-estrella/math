Resource audit

Numerical computations after wrapper repair used scripts/limited.py: two-CPU affinity, CPU 120 seconds per process, 140-second wall watchdog, sampled aggregate process-group RSS ceiling 6 GiB, 12 GiB address-space ceiling, MALLOC_ARENA_MAX=2. Full logs and receipts are retained. No Lean or leanchecker was invoked. No packages were installed. No background process is intended to remain at handback.

Deviations, retained rather than concealed:

- The initial extraction and second PDF batch used the inherited wrapper, which monitored the immediate process rather than the aggregate process group and did not explicitly set MALLOC_ARENA_MAX. It was replaced before the substantive numerical searches.
- The first PDF download/text extraction batch ran without the wrapper. The text converter printed warnings; downloads and text outputs remain retained, but converter stderr was not saved in a lane log for that first batch.
- While sandpile-6-6 was still running, an EIP pilot was started after an incomplete wait. The failed pilot and repaired atlas pass lasted about 0.38 and 0.47 seconds respectively. Thus the strict no-overlap instruction was breached. Subsequent heavy calls waited for recorded completion. Neither process approached the memory ceiling.
- The structured EIP pilot initially failed because its definition-loading namespace lacked a real __file__ path. It was fixed to pass the real eip.py script path; no directory was derived from stdin, and no write outside this lane resulted.

The sampling watchdog is not a cgroup guarantee against transient peaks. HTTP transfers used TLS verification and immutable timestamped receipt directories. Denied hosts inherited from the brief are recorded in outputs/denied-hosts.json; no denied HTTP route was retried.
