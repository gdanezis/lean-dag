"""Search for a commit disagreement under bypass (`docs/sync-auth.md` §7).

Needs `z3-solver`. `python3 sync-bypass-safety.py n f twins opts`, where opts is a
comma-separated list of `expose` (the exposure clause), `self` (honest blocks
reference their own author's block), `follow` (v reads only blocks it follows),
`hdr` (v holds the references of every block it follows), `hdr2` (v also holds
the references of a block one of whose referrers it follows), and `R=k`.

The leader L, by honest author 0, is at round 1, votes are at 2 and certificates
at 3, and the anchor A, by honest author 1, is at round R. Byzantine authors have
up to `twins` blocks a round. Node w holds every block and commits L directly: q
certificates of distinct authors, each referencing q votes. Node v holds every
honest block and some Byzantine ones; each block it holds has its references held
or bypassed. v does not commit L directly, and no certificate that v can check,
its votes held, is reachable from A through blocks v holds. `sat` prints such a
DAG; `unsat` means none exists at these sizes.
"""
import itertools, sys
from z3 import Bool, Solver, Or, And, Not, Implies, Sum, If, sat, PbGe, PbLe, AtMost, AtLeast

n = int(sys.argv[1]); f = int(sys.argv[2]); q = n - f
T = int(sys.argv[3]) if len(sys.argv) > 3 else 2
opts = set(sys.argv[4].split(',')) if len(sys.argv) > 4 else set()
HON = list(range(n - f)); BYZ = list(range(n - f, n))
R = int(dict(o.split('=') for o in opts if '=' in o).get('R', 4))
blocks = []   # (author, round, slot)
for r in range(1, R + 1):
    for a in range(n):
        for s in (range(T) if a in BYZ else range(1)):
            blocks.append((a, r, s))
idx = {b: i for i, b in enumerate(blocks)}
at = {r: [i for i, b in enumerate(blocks) if b[1] == r] for r in range(1, R + 1)}
L = idx[(0, 1, 0)]; A = idx[(1, R, 0)]
S = Solver()
ex = [Bool(f"e{i}") for i in range(len(blocks))]
ref = {}
for r in range(2, R + 1):
    for b in at[r]:
        for x in at[r - 1]:
            ref[b, x] = Bool(f"r{b}_{x}")
            S.add(Implies(ref[b, x], And(ex[b], ex[x])))
for i, (a, r, s) in enumerate(blocks):
    if a in HON:
        S.add(ex[i])
    if r == 1:
        continue
    # one reference per author, at least q authors
    refa = []
    for a2 in range(n):
        xs = [ref[i, x] for x in at[r - 1] if blocks[x][0] == a2]
        S.add(AtMost(*xs, 1))
        refa.append(Or(xs))
    S.add(Implies(ex[i], AtLeast(*refa, q)))
    if 'self' in opts and a in HON:
        S.add(ref[i, idx[(a, r - 1, 0)]])
# history (ancestry) for the exposure clause
anc = {}
for r in range(1, R + 1):
    for b in at[r]:
        for x in [j for rr in range(1, r) for j in at[rr]]:
            if blocks[x][1] == r - 1:
                anc[b, x] = ref[b, x]
            else:
                anc[b, x] = Or([And(ref[b, y], anc[y, x]) for y in at[r - 1]])
if 'expose' in opts:
    # a block whose history holds two blocks of an author references no block of it
    for b in [i for r in range(2, R + 1) for i in at[r]]:
        r = blocks[b][1]
        for a2 in BYZ:
            for rr in range(1, r - 1):
                tw = [x for x in at[rr] if blocks[x][0] == a2]
                for x, y in itertools.combinations(tw, 2):
                    for z in at[r - 1]:
                        if blocks[z][0] == a2:
                            S.add(Not(And(anc[b, x], anc[b, y], ref[b, z])))
            # twins among the references' round
            tw = [x for x in at[r - 1] if blocks[x][0] == a2]
            for x, y in itertools.combinations(tw, 2):
                pass  # one reference per author already excludes them

def authors_ge(conds, k):
    # conds: list of (block, cond); at least k distinct authors with some cond true
    by = {}
    for x, c in conds:
        by.setdefault(blocks[x][0], []).append(c)
    return AtLeast(*[Or(cs) for cs in by.values()], k) if len(by) >= k else False

vote = {y: ref[y, L] for y in at[2]}
# w holds everything: certificates and the direct commit
certW = {c: And(ex[c], authors_ge([(y, And(ref[c, y], vote[y])) for y in at[2]], q)) for c in at[3]}
S.add(authors_ge([(c, certW[c]) for c in at[3]], q))
# v's holdings
hv = [Bool(f"h{i}") for i in range(len(blocks))]
for i, (a, r, s) in enumerate(blocks):
    S.add(Implies(hv[i], ex[i]))
    if a in HON:
        S.add(hv[i])
byp = {}
for r in range(1, R):
    for x in at[r]:
        byp[x] = authors_ge([(y, And(hv[y], Not(ref[y, x]))) for y in at[r + 1]], q)
for r in range(2, R + 1):
    for b in at[r]:
        for x in at[r - 1]:
            if 'hdr2' in opts:
                # v also holds the references of a block one of whose referrers it
                # follows: it reads a bypassed block's references, and stops there
                fol = lambda z: (And(hv[z], Not(byp[z])) if z in byp else hv[z])
                ups = [fol(y) for y in at.get(r + 1, []) if (y, b) in ref]
                full = Or([fol(b)] + [And(fol(y), ref[y, b]) for y in at.get(r + 1, [])])
                S.add(Implies(And(full, ref[b, x]), hv[x]))
            elif 'hdr' in opts:
                # v holds every reference of a block it holds and does not find
                # bypassed; it stops only below a bypassed block
                fol = And(hv[b], Not(byp[b])) if b in byp else hv[b]
                S.add(Implies(And(fol, ref[b, x]), hv[x]))
            else:
                S.add(Implies(And(hv[b], ref[b, x]), Or(hv[x], byp[x])))
# what v reads: 'follow' reads only blocks it follows (held and not bypassed);
# otherwise it reads every block it holds
readable = {x: (And(hv[x], Not(byp[x])) if 'follow' in opts and x in byp else hv[x])
            for x in range(len(blocks))}
certV = {c: And(hv[c], authors_ge([(y, And(ref[c, y], vote[y], readable[y])) for y in at[2]], q))
         for c in at[3]}
# v does not commit L directly, and finds no certificate through A
S.add(Not(authors_ge([(c, certV[c]) for c in at[3]], q)))
# v reaches from A through the blocks it reads
reach = {y: (y == A) for y in at[R]}
for r_ in range(R - 1, 2, -1):
    for x in at[r_]:
        reach[x] = Or([And(reach[y], readable[y] if y != A else True, ref[y, x])
                       for y in at[r_ + 1]])
for c in at[3]:
    S.add(Not(And(reach[c], readable[c], certV[c])))
r = S.check()
print(f"n={n} f={f} twins={T} opts={sorted(opts)}: {r}")
if r == sat:
    M = S.model()
    tv = lambda e: bool(M.eval(e, model_completion=True))
    def name(i):
        a_, r_, s_ = blocks[i]
        return (('L' if i == L else '') + ('h' if a_ in HON else 'B') + f"{a_}.{r_}"
                + (f"'{s_}" if s_ else ''))
    for r_ in range(1, R + 1):
        for i in at[r_]:
            if not tv(ex[i]):
                continue
            rs = [name(x) for x in at[r_ - 1] if (i, x) in ref and tv(ref[i, x])] if r_ > 1 else []
            tags = []
            if r_ == 2 and tv(vote[i]): tags.append('vote')
            if r_ == 3 and tv(certW[i]): tags.append('cert@w')
            if r_ == 3 and tv(certV[i]): tags.append('cert@v')
            if not tv(hv[i]): tags.append('not held by v')
            if i in byp and tv(byp[i]): tags.append('bypassed@v')
            print(f"  {name(i):8} refs {rs} {' '.join(tags)}")
