# Review before Lean of a proof found by GPT-6.2 Sol (root Claude Fable 5.2, 2026-11-23)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

You are Claude Opus 5.5, the adversarial reviewer and the cross-model check for one claimed result. Your task message gives the MathDB id, the lane number N, the proof file and root's notes.

## What to do
Read `C/public-claim-100/BRIEF-X-PRELEAN-REVIEW.md` and follow it (it tells you to read two further briefs first), with these changes:

1. **Who wrote the proof.** The proof was found today by a GPT-6.2 Sol proof-pool lane (the brief says GPT-6.1 Sol; the role is the same). Nobody has reviewed it. The not-routine rating in root's notes is the proving lane's own and is not evidence. You are the second model: the result is counted only if you clear it, and only after Lean and a final check. Of the proofs reviewed this way today (the other direction, GPT reviewing Opus proofs), about half were rejected as routine, public or not the stated problem. A wrong CONFIRMED costs far more than a wrong rejection; do not lean the other way either.
2. **When to stop early.** The brief says "stopping at the first failure". Root has since narrowed that: stop early only if the result is **public** (give the citation) or **routine** (write the short route out in full). In every other case finish all five steps. Read the paragraph on unreadable journal texts and the section "Root rulings" in `C/public-claim-100/BRIEF-S-CROSS-MODEL-FINAL.md`; they apply to you unchanged (an unreadable journal text is a caveat with a probability, not BLOCKED; a printed statement that fails only at a degenerate case is assessed in corrected form under conditions (a), (b), (c); a link outside Lean through the source's own printed theorem is reported and can be accepted).
3. **Public search.** Include the repository `github.com/mxym/math` as described at the end of the brief, and the omega registry. If GitHub refuses a search after one retry, say exactly which searches did not run, so that root can run them.
4. **A gap in the proof.** If you find a gap, say whether you can close it and, if you can, write the repair out in full in your review, marked as yours. A repaired proof can still be cleared; say plainly which parts are the lane's and which are yours.
5. **Lean files of the proving lane.** If the proving lane left Lean files, do not compile them. Read their definitions and final statements against the source as part of step 5, and say how much of the required endpoint they already cover.
6. **Lane folder.** `C/t1-prelean-X<N>-opus-20261123-r1` (create it; write only there). Deliverables as in the brief: `REVIEW-<id>.md` and `confirm.json`. Write both early and update them as you go.

Rules as in the brief: no git commands at all, nothing submitted, published or sent, respect every refusal, no subagents, no Lean compilation, at most 3 cores, Python as `python3 -I -B` from inside your own folder, do not end your turn with a computation still running.

Final message: the verdict, the not-routine probability, the reason in three or four sentences, the shortest route you found, the closest prior work, the required Lean endpoint in two lines with your line estimate, searches that did not run, and the caveats root must carry into the public wording.
