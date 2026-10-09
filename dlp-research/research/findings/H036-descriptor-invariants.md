# H036 address-derived descriptor invariants

Native Sol proposed and native Astra independently checked the following
literal-contract optimization. Root integrated it into H036-complete-ledger.md.
It does not describe the frozen experiment or every possible search schedule.

With no holes in candidate leaf insertion, one-based code c encodes ordinalc-1;
divide by2 for edge ordinal, take parity for sign. Current-query descriptor is
already known. The terminal matching key is not inserted.
For nonzero-target H019 per-index order baby0,giant0,baby1,giant1,..., baby0=O
is skipped, leaving code1=giant0,code2=baby1,code3=giant1. Thus parity supplies
role and integer division by2 supplies index. Split-role codes encode baby
indexc or giant indexc-1. Mask/index operations and recovery reconstruction
remain paid, even though descriptor storage is removed.

Required invariants: no future center insertion; all unsuccessful keys inserted,
including same-role duplicate keys; giant infinity and valid cross-role equality
terminate; first null candidate collision clears and falls back afresh; fallback
resets numbering; shifted targetO returns before arena creation; resource
interruption is terminal. H034 seed checks exclude leaf exceptional sources;
H019 arithmetic exception dispatch preserves the scheduled point and index.

Records then contain key and next code only. Traversal knows current code, so
role-first access needs no stored tag, but the branch and selective-access layout
are real costs. Next-code widths, sentinels, finite rounding, scratch and headers
must still fit. This strengthens the comparator and revises the earlier capacity
admission; it is not an executable ECDLP improvement.
