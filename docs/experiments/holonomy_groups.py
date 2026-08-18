"""Experiment 2: holonomy-style group cyclicity for (NonCrossing w, Config w).

The holonomy decomposition's groups act on BRICK FAMILIES (sets of subsets),
via elements that permute the bricks but may collapse within bricks.  Localized
cyclicity on single subsets (experiment 1) does not formally cover this.

Test here, for every reachable subset S (closure of {Q} under the monoid):
  bricks(S)   := maximal proper reachable subsets T < S  (holonomy bricks)
  HolGrp(S)   := permutations of bricks(S) induced by monoid elements m with
                 m(S) = S OR m(S) <= S mapping each brick ONTO a brick
                 (the holonomy group condition: m permutes the brick family
                 setwise: {m(T) : T in bricks} = bricks)
  check: HolGrp(S) cyclic?

Also the stricter/looser variants:
  V1: m arbitrary in M with {m(T): T in bricks(S)} = bricks(S)
  V2: only m with m(S) = S (bijective on S)  [subgroup of V1's]
"""

import itertools
from collections import Counter
from localized_cyclicity import build_monoid


def perm_closure_is_cyclic(perms):
    n = len(perms)
    for g in perms:
        gd = dict(g)
        seen = set()
        curd = dict(g)
        while frozenset(curd.items()) not in seen:
            seen.add(frozenset(curd.items()))
            curd = {s: gd[curd[s]] for s in curd}
        if len(seen) == n:
            return True
    return n <= 1


def analyze(W):
    configs, gens, monoid = build_monoid(W, verbose=False)
    nQ = len(configs)
    Q = tuple(range(nQ))

    reach = set()
    start = frozenset(Q)
    frontier = [start]
    reach.add(frozenset(Q))
    while frontier:
        new = []
        for S in frontier:
            for m in monoid:
                T = frozenset(m[s] for s in S)
                if T not in reach:
                    reach.add(T)
                    new.append(T)
        frontier = new

    bad_v1 = []
    bad_v2 = []
    stats = Counter()
    for S in reach:
        if len(S) <= 1:
            continue
        proper = [T for T in reach if T < S]
        bricks = [T for T in proper if not any(T < U for U in proper)]
        if not bricks:
            continue
        bricks_set = set(bricks)
        perms_v1 = set()
        perms_v2 = set()
        for m in monoid:
            imgs = [frozenset(m[s] for s in T) for T in bricks]
            if set(imgs) == bricks_set and len(set(imgs)) == len(bricks):
                p = frozenset(zip(range(len(bricks)),
                                  [bricks.index(t) for t in imgs]))
                perms_v1.add(p)
                if frozenset(m[s] for s in S) == S:
                    perms_v2.add(p)
        ok1 = perm_closure_is_cyclic(perms_v1)
        ok2 = perm_closure_is_cyclic(perms_v2)
        stats[(len(S), len(bricks), len(perms_v1), ok1)] += 1
        if not ok1:
            bad_v1.append((sorted(S), len(perms_v1)))
        if not ok2:
            bad_v2.append((sorted(S), len(perms_v2)))

    print(f"W={W}: reachable={len(reach)}")
    print(f"  V1 (any m permuting bricks): failures={len(bad_v1)}")
    for s, o in bad_v1[:4]:
        print("    non-cyclic order", o, "on S=", s)
    print(f"  V2 (m bijective on S): failures={len(bad_v2)}")
    print("  (|S|, #bricks, |HolGrpV1|, cyclic) counts:",
          dict(sorted(stats.items())))


if __name__ == "__main__":
    for W in (2, 3):
        analyze(W)
        print()
