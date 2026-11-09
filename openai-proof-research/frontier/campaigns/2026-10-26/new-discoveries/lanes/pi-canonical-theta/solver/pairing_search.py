#!/usr/bin/env python3
"""Search for pairing (perfect matching + same/reverse response rule) strategies.

For P2-win boards (m even): enumerate perfect matchings M of the m edges and an
orientation rule per pair (respond with same digit or reversed digit); P2
responds to every P1 move on the partner edge. Verify by exhaustive simulation.

For P1-win boards (m odd): P1 opens with edge e0 (some direction rule), then
pairs the remaining edges the same way.

A response is a function: given opponent move (e, d), respond (partner(e),
rule(pair) == 'same' ? d : 3-d). The response must be legal every time; if not,
the strategy fails.
"""
import sys
from analyze113 import Board

def perfect_matchings(items):
    items = tuple(items)
    if not items:
        yield []
        return
    first = items[0]
    for i in range(1, len(items)):
        second = items[i]
        rest = items[1:i] + items[i+1:]
        for sub in perfect_matchings(rest):
            yield [(first, second)] + sub

def make_pairing_strategy(board, matching, rules, opener=None, opener_dir=None):
    partner = {}
    for (a, b) in matching:
        partner[a] = b
        partner[b] = a
    def strat(state, bd):
        # who is to move; if opener set and state == 0 -> opener move
        if opener is not None and state == 0:
            return (opener, opener_dir)
        tri = bd.digits(state)
        # find opponent's last move: the single edge whose digit changed... we
        # cannot know from state alone; instead: respond to the most recent move.
        # We reconstruct: the strategy is called at winner's turn; the opponent
        # just moved edge e with digit d. We find it by diffing? Not available.
        # Instead we pass through a wrapper in verify (we use verify2 below).
        raise NotImplementedError
    return strat

def verify_pairing(board, matching, rules, winner, opener=None, opener_dir=None):
    """Exhaustive: winner responds on partner. Returns True if winner wins all plays."""
    partner = {}
    for (a, b) in matching:
        partner[a] = b
        partner[b] = a
    stats = {'nodes': 0, 'cell': 0, 'last': 0, 'illegal': 0}
    m = board.m
    pw3 = board.pw3

    def rec(state, last_move):
        stats['nodes'] += 1
        p = board.player(state)
        tri = board.digits(state)
        moves = []
        for e in range(m):
            if tri[e]:
                continue
            for d in (1, 2):
                eff = board.move_effects(state, e, d)
                if eff:
                    moves.append((e, d, eff))
        if not moves:
            last = 3 - p
            if last == winner:
                stats['last'] += 1
                return True
            return False
        if p == winner:
            if opener is not None and state == 0:
                e, d = opener, opener_dir
            else:
                if last_move is None:
                    return False
                e0, d0 = last_move
                e = partner[e0]
                if tri[e]:
                    return False
                d = d0 if rules[(e0, e)] == 0 else 3 - d0
            eff = board.move_effects(state, e, d)
            if eff is None:
                stats['illegal'] += 1
                return False
            if eff == 'win':
                stats['cell'] += 1
                return True
            return rec(state + d * pw3[e], None)
        else:
            for (e, d, eff) in moves:
                if eff == 'win':
                    return False
                if not rec(state + d * pw3[e], (e, d)):
                    return False
            return True

    ok = rec(0, None)
    return ok, stats

def search_pairings(k, outer, winner, verbose=False, limit=200000):
    b = Board(1, 3, k, outer)
    m = b.m
    assert m % 2 == (0 if winner == 2 else 1), (m, winner)
    found = []
    if winner == 2:
        matchings = list(perfect_matchings(range(m)))
        if len(matchings) > limit:
            print(f"  too many matchings ({len(matchings)}), skipping")
            return found
        for M in matchings:
            for rules_bits in range(1 << len(M)):
                rules = {}
                for i, pair in enumerate(M):
                    rules[pair] = rules_bits & 1
                    rules[(pair[1], pair[0])] = rules_bits & 1
                    rules_bits >>= 1
                ok, stats = verify_pairing(b, M, rules, 2)
                if ok:
                    found.append((M, dict(rules), stats))
                    if verbose:
                        names = b.edge_names()
                        print("  P2 pairing WIN:", [(names[a], names[b], 'same' if r==0 else 'rev') for (a,b),r in rules.items() if a<b])
                    break  # any rule set for this matching; but keep searching matchings? break all
            if found:
                break
    else:
        # P1 opens, then pairs remaining
        matchings_by_open = {}
        names = b.edge_names()
        for opener in range(m):
            rest = [e for e in range(m) if e != opener]
            Ms = list(perfect_matchings(rest))
            for M in Ms:
                for ob in (1, 2):
                    for rules_bits in range(1 << len(M)):
                        rules = {}
                        for i, pair in enumerate(M):
                            rules[pair] = rules_bits & 1
                            rules[(pair[1], pair[0])] = rules_bits & 1
                            rules_bits >>= 1
                        ok, stats = verify_pairing(b, M, rules, 1, opener=opener, opener_dir=ob)
                        if ok:
                            found.append((opener, ob, M, dict(rules), stats))
                            if verbose:
                                print(f"  P1 opener {names[opener]} dir {'F' if ob==1 else 'B'} pairing:",
                                      [(names[a], names[b], 'same' if r==0 else 'rev') for (a,b),r in rules.items() if a<b])
                            break
                    if found and found[-1][0] == opener:
                        break
                if found and found[-1][0] == opener:
                    break
            if len(found) >= 1:
                break
    return found

if __name__ == '__main__':
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    for k in range(2, kmax + 1):
        m = k + 4
        w = 1 if m % 2 else 2
        for outer in range(3):
            print(f"Theta(1,3,{k}) outer={outer}: winner P{w}")
            f = search_pairings(k, outer, w, verbose=True)
            if not f:
                print("  NO pairing strategy found")
