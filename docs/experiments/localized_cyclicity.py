"""Decisive experiment for the E2 leaf (letterWordACC_impl).

Tests the LOCALIZED CYCLICITY conjecture that the explicit holonomy-style
cascade needs:

  For every reachable subset S of Config w, the group
      G_S = { m|_S : m in NonCrossing w, m(S) = S (setwise, hence bijectively) }
  of permutations of S is CYCLIC.

Also collects the data needed to gauge the holonomy depth:
  - the lattice of reachable image sets (closure of {Q} under all m in M);
  - for each reachable S, |S|, |G_S|, cyclic?;
  - the aperiodicity check for the "collapse" quotient: whether non-invertible
    steps between reachable sets can cycle without group content (they cannot,
    by cardinality, but we record the DAG structure by size).

Method: enumerate all depth-1 non-crossing layer maps for width w (same
convention as iter-15's hmv_explore.py: outputs read cyclic-interval-like
non-crossing windows with AND/OR, empty window = const 0/1), close under
composition to get M = NonCrossing w, then run the tests.
"""

import itertools
import sys
from math import gcd

def get_non_crossing_graphs(W):
    all_edges = [(i, j) for i in range(W) for j in range(W)]
    y_assignments = []

    def is_non_crossing(edges):
        if not edges:
            return True
        def search(idx, current_y, edges_sorted):
            if idx == len(edges_sorted):
                y0 = y_assignments[0]
                y_last = y_assignments[-1]
                return y_last <= y0 + W
            i, j = edges_sorted[idx]
            y = current_y
            while y % W != j:
                y += 1
            y_assignments.append(y)
            nxt = y if (idx + 1 < len(edges_sorted) and edges_sorted[idx + 1][0] != i) else y + 1
            # allow same right node for different left nodes (y equal ok when i differs),
            # but for same i the next y must be strictly larger
            if idx + 1 < len(edges_sorted) and edges_sorted[idx + 1][0] == i:
                nxt = y + 1
            else:
                nxt = y
            if search(idx + 1, nxt, edges_sorted):
                return True
            y_assignments.pop()
            return False

        for shift in range(W):
            shifted = sorted(((i + shift) % W, j) for (i, j) in edges)
            y_assignments.clear()
            if search(0, 0, shifted):
                return True
        return False

    graphs = set()
    for k in range(len(all_edges) + 1):
        for subset in itertools.combinations(all_edges, k):
            if is_non_crossing(subset):
                graphs.add(frozenset(subset))
    return graphs


def build_monoid(W, verbose=True):
    graphs = get_non_crossing_graphs(W)
    configs = list(itertools.product([0, 1], repeat=W))
    cidx = {c: i for i, c in enumerate(configs)}

    maps = set()
    for g in graphs:
        inputs_by_j = {j: set() for j in range(W)}
        for (i, j) in g:
            inputs_by_j[j].add(i)
        choices = []
        for j in range(W):
            inp = frozenset(inputs_by_j[j])
            if not inp:
                choices.append([(0, 0), (0, 1)])
            elif len(inp) == 1:
                choices.append([(1, inp)])
            else:
                choices.append([(1, inp), (2, inp)])
        for comb in itertools.product(*choices):
            maps.add(comb)

    def evaluate(m, c):
        out = []
        for j in range(W):
            t, inp = m[j]
            if t == 0:
                out.append(inp)
            elif t == 1:
                out.append(int(all(c[i] for i in inp)))
            else:
                out.append(int(any(c[i] for i in inp)))
        return tuple(out)

    def to_tt(m):
        return tuple(cidx[evaluate(m, c)] for c in configs)

    gens = set(to_tt(m) for m in maps)
    monoid = set(gens)
    frontier = list(gens)
    while frontier:
        new = []
        for t1 in frontier:
            for g in gens:
                t = tuple(g[t1[i]] for i in range(len(configs)))  # t1 then g
                if t not in monoid:
                    monoid.add(t)
                    new.append(t)
        frontier = new
    if verbose:
        print(f"W={W}: graphs={len(graphs)} gen_maps={len(gens)} monoid={len(monoid)}")
    return configs, sorted(gens), sorted(monoid)


def is_cyclic_permgroup(perms):
    """perms: set of tuples (permutations of a subset given as dict-like tuples).
    Represented as frozensets of (src, dst) pairs. Returns (is_group_cyclic, order)."""
    n = len(perms)
    for g in perms:
        # order of g
        gen = set()
        cur = g
        gd = dict(g)
        curd = dict(g)
        while frozenset(curd.items()) not in gen:
            gen.add(frozenset(curd.items()))
            curd = {s: gd[curd[s]] for s in curd}
        if len(gen) == n:
            return True, n
    return (n == 1), n


def analyze(W):
    configs, gens, monoid = build_monoid(W)
    nQ = len(configs)
    Q = tuple(range(nQ))

    # reachable image sets: closure of {Q} under all m in M
    reach = set()
    start = frozenset(Q)
    frontier = [start]
    reach.add(start)
    while frontier:
        new = []
        for S in frontier:
            for m in monoid:
                T = frozenset(m[s] for s in S)
                if T not in reach:
                    reach.add(T)
                    new.append(T)
        frontier = new
    print(f"W={W}: reachable image sets: {len(reach)} (sizes: ", end="")
    from collections import Counter
    print(sorted(Counter(len(S) for S in reach).items()), ")")

    # localized cyclicity: for each reachable S, the permutations of S realized
    bad = []
    group_sizes = Counter()
    for S in reach:
        Sl = sorted(S)
        perms = set()
        for m in monoid:
            img = [m[s] for s in Sl]
            if set(img) == set(Sl):
                perms.add(frozenset(zip(Sl, img)))
        ok, order = is_cyclic_permgroup(perms)
        group_sizes[(len(S), order, ok)] += 1
        if not ok:
            bad.append((Sl, order))
    print(f"W={W}: localized cyclicity over {len(reach)} sets: ", end="")
    if not bad:
        print("ALL CYCLIC ✓")
    else:
        print(f"FAILURES: {len(bad)}")
        for Sl, order in bad[:5]:
            print("   non-cyclic group of order", order, "on S=", Sl)
    print("   (|S|, |G_S|, cyclic) -> count:", dict(sorted(group_sizes.items())))

    # extra: setwise-stabilizer groups for ALL subsets (not only reachable) — is
    # reachability essential?
    bad_all = 0
    checked = 0
    for r in range(1, nQ + 1):
        for Sl in itertools.combinations(Q, r):
            checked += 1
            perms = set()
            for m in monoid:
                img = [m[s] for s in Sl]
                if set(img) == set(Sl):
                    perms.add(frozenset(zip(Sl, img)))
            ok, order = is_cyclic_permgroup(perms)
            if not ok:
                bad_all += 1
    print(f"W={W}: over ALL {checked} subsets: non-cyclic stabilizer groups: {bad_all}")
    return len(bad) == 0, bad_all


if __name__ == "__main__":
    for W in (2, 3):
        ok, bad_all = analyze(W)
        print()
