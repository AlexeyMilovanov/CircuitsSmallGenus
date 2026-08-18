"""EXACT certified single layers at W=4 per the Lean semantics, then closure+tests.

A full-width layer table: for each target position p one of
  const b                     (literal / empty gate; no arcs)
  (op, P) with op in AND/OR, P subset of positions, 1 <= |P| <= 2   (HMVNormal)
Arcs: (q -> p) for q in P(p).  Certificate (standard listings WLOG): exists
orderings within source blocks (outgoing arcs of q, in source order q=0..3)
and within target blocks (incoming arcs of p, in order p=0..3) such that the
two concatenations are cyclic rotations of each other.

Then: translate-closure of the exact generator set; tests over subsets of
sizes 2..5: interval-count preservation (C), interval-wise action (I),
min-layer rigidity (RIG), and cyclicity of every realized group (CYC).
"""
import itertools, time
from collections import defaultdict
import numpy as np

W = 4
configs = list(itertools.product([0, 1], repeat=W))
cidx = {c: i for i, c in enumerate(configs)}
N = len(configs)

def cyc_variants(word):
    n = len(word)
    return {tuple(word[i:] + word[:i]) for i in range(n)}

def certified(table):
    """table: list of W entries: ('c', b) or (op, tuple(P))."""
    arcs = []
    for p, ent in enumerate(table):
        if ent[0] == 'c':
            continue
        for q in ent[1]:
            arcs.append((q, p))
    if not arcs:
        return True
    out_blocks = [[a for a in arcs if a[0] == q] for q in range(W)]
    in_blocks = [[a for a in arcs if a[1] == p] for p in range(W)]
    # order choices within blocks
    def orderings(blocks):
        pools = [list(itertools.permutations(b)) if len(b) > 1 else [tuple(b)]
                 for b in blocks]
        for combo in itertools.product(*pools):
            yield tuple(a for blk in combo for a in blk)
    src_words = set()
    for wd in orderings(out_blocks):
        src_words |= cyc_variants(list(wd))
    for wd in orderings(in_blocks):
        if tuple(wd) in src_words:
            return True
    return False

def table_map(table):
    def f(c):
        out = []
        for ent in table:
            if ent[0] == 'c':
                out.append(ent[1])
            elif ent[0] == 'and':
                out.append(int(all(c[q] for q in ent[1])))
            else:
                out.append(int(any(c[q] for q in ent[1])))
        return tuple(out)
    return bytes(cidx[f(c)] for c in configs)

entry_choices = [('c', 0), ('c', 1)]
for size in (1, 2):
    for P in itertools.combinations(range(W), size):
        entry_choices.append(('and', P))
        if size == 2:
            entry_choices.append(('or', P))

t0 = time.time()
gens = set()
ncert = 0
for table in itertools.product(entry_choices, repeat=W):
    if certified(list(table)):
        ncert += 1
        gens.add(table_map(list(table)))
print(f"tables certified: {ncert}, distinct maps: {len(gens)}, "
      f"{round(time.time()-t0)}s", flush=True)

ident = bytes(range(N))
gens.add(ident)
def pad(t): return t + bytes(range(len(t), 256))
gpads = [pad(g) for g in sorted(gens)]
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
print("EXACT monoid:", len(monoid), "in", round(time.time() - t0, 1), "s", flush=True)

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

def subset_le(c1, c2):
    return all(a <= b for a, b in zip(configs[c1], configs[c2]))

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
noncyc, cfail, ifail, rigfail = [], [], [], []
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
        # per-perm structural tests + rigidity bookkeeping
        IS = sorted({p for x in S for p in pieces(x)})
        layers = []
        rest = set(IS)
        while rest:
            mins = {a for a in rest if not any(b != a and subset_le(b, a) for b in rest)}
            layers.append(sorted(mins))
            rest -= mins
        L0 = layers[0] if layers else []
        sig_map = {}
        for key, m in perms.items():
            if all(a == b for a, b in key):
                continue
            if not all(maxints(configs[m[x]]) == maxints(configs[x]) for x in S):
                if len(cfail) < 6: cfail.append((S, key))
                continue
            okI = True
            for x in S:
                if sorted(pieces(m[x])) != sorted(m[p] for p in pieces(x)):
                    okI = False
                    if len(ifail) < 6: ifail.append((S, key, x))
                    break
            if not okI:
                continue
            phi = {a: m[a] for a in IS}
            if sorted(phi.values()) != IS:
                continue
            sig0 = tuple(phi[a] for a in L0)
            sigall = tuple(phi[a] for a in IS)
            prev = sig_map.get(sig0)
            if prev is not None and prev != sigall:
                if len(rigfail) < 6: rigfail.append((S, sig0))
            sig_map[sig0] = sigall
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
print("RIG failures:", len(rigfail))
for S, sig0 in rigfail[:4]:
    print("  S = {", ",".join(show(x) for x in S), "} fixed layer-0 sig:",
          [show(a) for a in sig0])
