"""Fast exact monoid: grow a small generating set until it covers all certified
layers, closing with the small set each round (translate closure is O(|M|*|G0|))."""
import itertools, time, pickle
W = 4
configs = list(itertools.product([0, 1], repeat=W))
cidx = {c: i for i, c in enumerate(configs)}
N = len(configs)
def tt(f): return bytes(cidx[f(c)] for c in configs)

def cyc_variants(word):
    n = len(word); return {tuple(word[i:] + word[:i]) for i in range(n)}
def certified(table):
    arcs = []
    for p, ent in enumerate(table):
        if ent[0] == 'c': continue
        for q in ent[1]: arcs.append((q, p))
    if not arcs: return True
    ob = [[a for a in arcs if a[0] == q] for q in range(W)]
    ib = [[a for a in arcs if a[1] == p] for p in range(W)]
    def orderings(blocks):
        pools = [list(itertools.permutations(b)) if len(b) > 1 else [tuple(b)]
                 for b in blocks]
        for combo in itertools.product(*pools):
            yield tuple(a for blk in combo for a in blk)
    src = set()
    for wd in orderings(ob): src |= cyc_variants(list(wd))
    for wd in orderings(ib):
        if tuple(wd) in src: return True
    return False
def table_map(table):
    def f(c):
        out = []
        for ent in table:
            if ent[0] == 'c': out.append(ent[1])
            elif ent[0] == 'and': out.append(int(all(c[q] for q in ent[1])))
            else: out.append(int(any(c[q] for q in ent[1])))
        return tuple(out)
    return tt(f)

entry = [('c', 0), ('c', 1)]
for size in (1, 2):
    for P in itertools.combinations(range(W), size):
        entry.append(('and', P))
        if size == 2: entry.append(('or', P))
exact = []
for table in itertools.product(entry, repeat=W):
    t = list(table)
    if certified(t):
        exact.append(table_map(t))
exact_set = sorted(set(exact))
print("exact gens:", len(exact_set), flush=True)

def pad(t): return t + bytes(range(len(t), 256))
ident = bytes(range(N))

G0 = set([ident])
for k in configs: G0.add(tt(lambda c, k=k: k))
for i in range(W):
    for op in ("and", "or"):
        def f(c, i=i, op=op):
            out = list(c); a, b = c[i], c[(i + 1) % W]
            out[i] = (a & b) if op == "and" else (a | b)
            return tuple(out)
        G0.add(tt(f))
for s in range(1, W):
    G0.add(tt(lambda c, s=s: tuple(c[(i + s) % W] for i in range(W))))
for i in range(W):
    G0.add(tt(lambda c, i=i: tuple(c[i] if j == (i + 1) % W else c[j] for j in range(W))))
for i in range(W):
    for b in (0, 1):
        G0.add(tt(lambda c, i=i, b=b: tuple(b if j == i else c[j] for j in range(W))))

rounds = 0
while True:
    rounds += 1
    gp = [pad(g) for g in sorted(G0)]
    monoid = set(G0); frontier = list(G0)
    t0 = time.time()
    while frontier:
        new = []
        for t in frontier:
            for g in gp:
                t2 = t.translate(g)
                if t2 not in monoid:
                    monoid.add(t2); new.append(t2)
        frontier = new
    missing = [g for g in exact_set if g not in monoid]
    print(f"round {rounds}: |G0|={len(G0)} closure={len(monoid)} "
          f"missing={len(missing)} ({round(time.time()-t0)}s)", flush=True)
    if not missing:
        break
    # add a batch of missing generators
    for g in missing[:40]:
        G0.add(g)

with open("/home/lesha/oq3-experiments/exact_monoid_w4.pkl", "wb") as f:
    pickle.dump(sorted(monoid), f)
print("EXACT MONOID SIZE:", len(monoid), "saved", flush=True)
