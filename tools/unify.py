#!/usr/bin/env python3
"""Cycle-1 mechanical unification: monolith_gen (read-only) -> unified/SurfaceBlowup/**.
Plan file logs/plan.json records file -> module assignment."""
import json, re, os, sys, heapq, collections
sys.path.insert(0, os.path.dirname(__file__))
from topics import topic

SRC = os.path.expanduser('~/prove2me_workspace/final/monolith_gen')
DST = os.path.expanduser('~/prove2me_workspace/final/unified')
LOGS = DST + '/logs'
CAP = int(os.environ.get('CAP', '1300'))

live = [l.strip() for l in open(LOGS + '/live_modules.txt') if l.strip()]
EXCLUDE = {'Thm_Gen_MainDvr'}  # rewritten by hand in Main.lean
live = [m for m in live if m not in EXCLUDE]
liveset = set(live)
nb = json.load(open(LOGS + '/node_batch.json'))

def path(m):
    return f"{SRC}/{'Definitions' if m.startswith('Def_') else 'Theorems'}/{m}.lean"

def read(m):
    return open(path(m)).read()

allmods = [f[:-5] for d in ('Definitions', 'Theorems') for f in os.listdir(f'{SRC}/{d}') if f.endswith('.lean')]
imports, body = {}, {}
for m in allmods:
    txt = read(m)
    imps, rest = [], []
    for line in txt.split('\n'):
        if line.startswith('import '):
            imps.append(line[7:].strip())
        else:
            rest.append(line)
    imports[m] = imps
    body[m] = '\n'.join(rest)

def short(i):
    i = i.replace('«', '').replace('»', '')
    return i.split('.', 1)[1] if i.startswith(('Definitions.', 'Theorems.')) else None

# transitive Mathlib imports over the ORIGINAL project import closure
memo = {}
def mathlib_closure(m):
    if m in memo: return memo[m]
    s = set(i for i in imports[m] if not short(i))
    for i in imports[m]:
        if short(i): s |= mathlib_closure(short(i))
    memo[m] = s
    return s

pmemo = {}
def proj_closure(m):
    if m in pmemo: return pmemo[m]
    s = set()
    for i in imports[m]:
        if short(i): s.add(short(i)); s |= proj_closure(short(i))
    pmemo[m] = s
    return s

# usage edges (constant level)
deps = collections.defaultdict(set)
for line in open(LOGS + '/edges_all.tsv'):
    a, b = line.strip().split('\t')
    a, b = short(a), short(b)
    if a in liveset and b in liveset and b in proj_closure(a):
        deps[a].add(b)
# MainDvr's deps are handled by Main.lean
users = collections.defaultdict(set)
for a in live:
    for b in deps[a]: users[b].add(a)

# topics
def batch(m):
    i, h = nb.get(m, ('?', []))
    if len(h) == 1: return h[0].replace('batch_', '').replace('.py', '')
    if h: return 'MULTI:' + ','.join(x.replace('batch_', '').replace('.py', '') for x in h)
    return 'NONE'
top = {m: topic(m, batch(m)) for m in live}
for _ in range(10):
    for m in live:
        if top[m] is None:
            c = collections.Counter(top[x] for x in deps[m] | users[m] if top[x])
            if c: top[m] = c.most_common(1)[0][0]
for m in live:
    if top[m] is None: top[m] = 'Blowup'

RANK = ['Basic', 'Formula', 'Algebra', 'Measure', 'Unramified', 'Surfaces', 'Blowup', 'Recursion',
        'Assembly', 'Reciprocity', 'FieldForm', 'Main']
lines = {m: body[m].count('\n') + 1 for m in live}

# Kahn topological order with topic priority
indeg = {m: len(deps[m]) for m in live}
order_idx = {m: i for i, m in enumerate(sorted(live))}
heap = [(RANK.index(top[m]), order_idx[m], m) for m in live if indeg[m] == 0]
heapq.heapify(heap)
topo = []
while heap:
    _, _, m = heapq.heappop(heap)
    topo.append(m)
    for u in users[m]:
        indeg[u] -= 1
        if indeg[u] == 0:
            heapq.heappush(heap, (RANK.index(top[u]), order_idx[u], u))
assert len(topo) == len(live), 'cycle?'

# greedy module assignment
modules = []        # list of dict(topic, files, lines)
modof = {}
cur = {}            # topic -> list of module indices open for that topic
for m in topo:
    t = top[m]
    req = max((modof[d] for d in deps[m]), default=-1)
    placed = False
    for idx in reversed(cur.get(t, [])):
        if idx >= req and modules[idx]['lines'] + lines[m] <= CAP:
            modules[idx]['files'].append(m); modules[idx]['lines'] += lines[m]; modof[m] = idx; placed = True
            break
        if idx < req: break
    if not placed:
        modules.append({'topic': t, 'files': [m], 'lines': lines[m]})
        modof[m] = len(modules) - 1
        cur.setdefault(t, []).append(len(modules) - 1)

print('modules', len(modules))
cnt = collections.Counter(x['topic'] for x in modules)
print(dict(cnt))
json.dump({'modules': modules, 'topic': top}, open(LOGS + '/plan_raw.json', 'w'), indent=1)

# ---- post-pass: dissolve small modules into a compatible neighbour ----
SMALL = int(os.environ.get('SMALL', '250'))
def req_of(f):
    return max((modof[d] for d in deps[f]), default=-1)
def minuser_of(f):
    return min((modof[u] for u in users[f]), default=10**9)
changed = True
while changed:
    changed = False
    for j, mj in enumerate(modules):
        if not mj['files'] or mj['lines'] >= SMALL: continue
        lo = max(req_of(f) for f in mj['files'] if True)
        # dependencies inside mj itself do not constrain
        lo = max([modof[d] for f in mj['files'] for d in deps[f] if modof[d] != j] + [-1])
        hi = min([modof[u] for f in mj['files'] for u in users[f] if modof[u] != j] + [10**9])
        cands = [i for i, mi in enumerate(modules) if i != j and mi['files'] and lo <= i <= hi
                 and mi['lines'] + mj['lines'] <= CAP + 300]
        if not cands: continue
        cands.sort(key=lambda i: (modules[i]['topic'] != mj['topic'], modules[i]['lines']))
        i = cands[0]
        for f in mj['files']: modof[f] = i
        modules[i]['files'] += mj['files']; modules[i]['lines'] += mj['lines']
        mj['files'] = []; mj['lines'] = 0
        changed = True
pos = {m: k for k, m in enumerate(topo)}
modules = [m for m in modules if m['files']]
for m in modules: m['files'].sort(key=lambda f: pos[f])
# re-index
modof = {f: k for k, m in enumerate(modules) for f in m['files']}
for k, m in enumerate(modules):
    for f in m['files']:
        for d in deps[f]: assert modof[d] <= k, (f, d)
print('after merge', len(modules), dict(collections.Counter(x['topic'] for x in modules)))
json.dump({'modules': modules, 'topic': top, 'deps': {k: sorted(v) for k, v in deps.items()}}, open(LOGS + '/plan.json', 'w'), indent=1)
for k, m in enumerate(modules): print(k, m['topic'], m['lines'], len(m['files']), m['files'][0][20:60])
