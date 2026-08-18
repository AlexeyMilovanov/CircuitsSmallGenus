"""Conservative-generator refutation check at W=4.

Generators whose membership in NonCrossing 4 is beyond doubt:
  * all 16 constant maps (constTrans_mem_nonCrossing, kernel-proved);
  * for each wire i and op in {AND, OR}: output i := op(in_i, in_{i+1 mod 4}),
    output j := in_j otherwise (a single certified fan-in-2 layer);
  * the identity.
Close fully (translate closure), then over ALL subsets of size 2..5:
  * find realized perms, close under composition, test cyclicity/abelianness;
  * test interval-count preservation (C) and interval-wise action (I).
Every failure here refutes the corresponding statement for the true monoid,
modulo only the pair-layer membership (constants are already formal).
"""
import itertools, time
from collections import defaultdict
import numpy as np

W = 4
configs = list(itertools.product([0, 1], repeat=W))
cidx = {c: i for i, c in enumerate(configs)}
N = len(configs)

def tt(f):
    return bytes(cidx[f(c)] for c in configs)

gens = set()
# constants
for k in configs:
    gens.add(tt(lambda c, k=k: k))
# adjacent-pair AND/OR at wire i (reading i, i+1)
for i in range(W):
    for op in ("and", "or"):
        def f(c, i=i, op=op):
            out = list(c)
            a, b = c[i], c[(i + 1) % W]
            out[i] = (a & b) if op == "and" else (a | b)
            return tuple(out)
        gens.add(tt(f))
ident = bytes(range(N))
gens.add(ident)
gens = sorted(gens)
print("conservative gens:", len(gens), flush=True)

def pad(t): return t + bytes(range(len(t), 256))
gpads = [pad(g) for g in gens]
monoid = set(gens)
frontier = list(gens)
t0 = time.time()
while frontier:
    new = []
    for t in frontier:
        for gp in gpads:
            t2 = t.translate(gp)
            if t2 not in monoid:
                monoid.add(t2)
                new.append(t2)
    frontier = new
    print("  monoid", len(monoid), flush=True)
print("closure done:", len(monoid), "in", round(time.time() - t0, 1), "s", flush=True)

pool = sorted(monoid)
M = np.frombuffer(b"".join(pool), dtype=np.uint8).reshape(len(pool), N)

def maxints(c):
    ones = [i for i in range(W) if c[i]]
    if not ones: return 0
    if len(ones) == W: return 1
    return sum(1 for i in ones if not c[(i - 1) % W])

def intervals_of(c):
    ones = set(i for i in range(W) if c[i])
    if not ones or len(ones) == W: return []
    res = []
    for i in sorted(ones):
        if (i - 1) % W not in ones:
            blk = [i]; j = (i + 1) % W
            while j in ones:
                blk.append(j); j = (j + 1) % W
            res.append(tuple(blk))
    return res

def iconf(I):
    return cidx[tuple(1 if i in I else 0 for i in range(W))]

def pieces(x):
    c = configs[x]
    if all(c): return [x]
    return [iconf(I) for I in intervals_of(c)]

def show(c): return "".join(str(b) for b in configs[c])

def close_group(perms, Ss):
    items = set(perms)
    changed = True
    while changed and len(items) < 5000:
        changed = False
        cur = list(items)
        for k1 in cur:
            d1 = dict(k1)
            for k2 in cur:
                d2 = dict(k2)
                k = tuple((x, d1[d2[x]]) for x in Ss)
                if k not in items:
                    items.add(k)
                    changed = True
    return items

def perm_order(key, Ss):
    d = dict(key); o = 1; cur = dict(d)
    while any(cur[x] != x for x in Ss):
        cur = {x: d[cur[x]] for x in Ss}; o += 1
    return o

order_hist = defaultdict(int)
noncyc = []
cfail, ifail = [], []
tested = 0
t0 = time.time()
for r in range(2, 6):
    for S in itertools.combinations(range(N), r):
        Ss = list(S)
        Sarr = np.array(S, dtype=np.uint8)
        imgs = M[:, Sarr]
        target = np.sort(Sarr)
        hits = np.nonzero((np.sort(imgs, axis=1) == target).all(axis=1))[0]
        if len(hits) == 0:
            continue
        perms = {}
        for h in hits:
            m = M[h]
            key = tuple((x, int(m[x])) for x in Ss)
            perms.setdefault(key, bytes(M[h]))
        for key, m in perms.items():
            if all(a == b for a, b in key): continue
            if not all(maxints(configs[m[x]]) == maxints(configs[x]) for x in S):
                if len(cfail) < 6: cfail.append((S, key))
            else:
                for x in S:
                    if sorted(pieces(m[x])) != sorted(m[p] for p in pieces(x)):
                        if len(ifail) < 6: ifail.append((S, key, x))
                        break
        if len(perms) <= 1:
            continue
        tested += 1
        G = close_group(set(perms), Ss)
        n = len(G)
        order_hist[n] += 1
        if not any(perm_order(k, Ss) == n for k in G):
            noncyc.append((S, n, sorted(perm_order(k, Ss) for k in G)))
    print(f"size {r} done, tested {tested}, {round(time.time()-t0)}s", flush=True)

print("\norder histogram:", dict(sorted(order_hist.items())))
print("NON-CYCLIC:", len(noncyc))
for S, n, orders in noncyc[:10]:
    print("  S = {", ",".join(show(x) for x in S), "} |G| =", n, "orders:", orders)
print("C failures:", len(cfail))
for S, key in cfail[:4]:
    print("  S = {", ",".join(show(x) for x in S), "}  e:",
          " ".join(f"{show(a)}->{show(b)}" for a, b in key if a != b))
print("I failures:", len(ifail))
for S, key, x in ifail[:4]:
    print("  S = {", ",".join(show(x) for x in S), "}  e:",
          " ".join(f"{show(a)}->{show(b)}" for a, b in key if a != b), " at x =", show(x))
