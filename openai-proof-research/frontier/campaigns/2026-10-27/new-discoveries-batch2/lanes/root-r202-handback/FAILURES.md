# Root integration failure and repair

Both integration tools were called sequentially, but the first returned an active shell session before completion. Starting the second then overlapped Git work. r202 staging succeeded, but its explicit-path commit failed with exit 128: `Unable to create '/home/mj-kang/Documents/Dev/math/.git/index.lock': File exists.` The guard reported exit 1, sampled peak group RSS 121352192 bytes and wall time 1.682922750012949 seconds. No lock was deleted and no caps were raised.

r204 completed its explicit-path commit as 8cf9e3b07d. Both sessions were collected before recovery. The r202 continuation insertion was made idempotent to preserve the already-written entry, and its unchanged frozen worker evidence and explicit-path integration were rerun only after both earlier commands ended. This is a root orchestration failure, not a mathematical or worker integrity failure.
