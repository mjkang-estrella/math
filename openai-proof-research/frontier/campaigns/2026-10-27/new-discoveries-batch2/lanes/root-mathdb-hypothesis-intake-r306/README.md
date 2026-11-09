# MathDB hypothesis intake

This offline check supports the user's requested parallel hypothesis assignments.
It does not solve mathematics, rank difficulty automatically, modify MathDB,
or certify novelty. It accepts normalized proposals from completed triage tasks.
The first live intake remains pending; no corpus coverage is claimed here.

Run `python3 -B intake.py accepted-exclusions.json proposals.json` under the
campaign helper guard. Fields are listed in `intake.py`. Each row represents one
literal hypothesis, not an entire MathDB page. Different hypotheses on the same
page remain distinct. Exact duplicate rows are flagged. A matching accepted-family
ID requires a scope comparison; it does not automatically exclude every question
on that page. Primary-source review and full-statement review are separate.

Root chooses among complete rows using the concrete mechanism, decisive next
calculation, certificate size and formal dependencies. Selection authorizes an
attempt, never credit. Prior and adaptation objections travel with every task.
Use a separate Pi GLM 5.3 Flash delegate task per selected hypothesis, standard
speed, and a new independent delegate task for any proposed full resolution.
Keep at least one breadth/inventory assignment advancing while useful coverage
work remains, within the total three-delegate limit. Completed handbacks, not
polling or partial active-worker files, trigger assignment changes.

The copied accepted-family index is administrative routing evidence only. Its
schema was inspected before copying during this turn; it is not a new scientific
input or independently revalidated acceptance record. The original and snapshot
are hash-bound during setup and rechecked in final verification.
