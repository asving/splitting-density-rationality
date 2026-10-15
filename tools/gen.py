#!/usr/bin/env python3
"""Generate unified/SurfaceBlowup/** from logs/plan.json (cycle-1 mechanical pass)."""
import json, re, os, sys, collections, glob
sys.path.insert(0, os.path.dirname(__file__))
from names import NAMES
SRC = os.path.expanduser('~/prove2me_workspace/final/monolith_gen')
DST = os.path.expanduser('~/prove2me_workspace/final/unified')
ML = DST + '/.lake/packages/mathlib'
plan = json.load(open(DST + '/logs/plan.json'))
modules = plan['modules']
deps = {k: set(v) for k, v in plan['deps'].items()}

def path(m):
    return f"{SRC}/{'Definitions' if m.startswith('Def_') else 'Theorems'}/{m}.lean"

def short(i):
    i = i.replace('«', '').replace('»', '')
    return i.split('.', 1)[1] if i.startswith(('Definitions.', 'Theorems.')) else None

imports, body = {}, {}
for d in ('Definitions', 'Theorems'):
    for f in os.listdir(f'{SRC}/{d}'):
        if not f.endswith('.lean'): continue
        m = f[:-5]
        imps, rest = [], []
        for line in open(f'{SRC}/{d}/{f}').read().split('\n'):
            (imps if line.startswith('import ') else rest).append(line[7:].strip() if line.startswith('import ') else line)
        imports[m], body[m] = imps, '\n'.join(rest)

memo = {}
def mathlib_closure(m):
    if m in memo: return memo[m]
    s = set(i for i in imports[m] if not short(i))
    for i in imports[m]:
        if short(i): s |= mathlib_closure(short(i))
    memo[m] = s
    return s

# Mathlib public-import graph for transitive reduction
mlpub = {}
def ml_pub(mod):
    if mod in mlpub: return mlpub[mod]
    p = None
    for root in (ML, ML + '/.lake/packages/batteries', DST + '/.lake/packages/batteries', DST + '/.lake/packages/aesop',
                 DST + '/.lake/packages/plausible', DST + '/.lake/packages/Qq', DST + '/.lake/packages/proofwidgets',
                 DST + '/.lake/packages/importGraph', DST + '/.lake/packages/LeanSearchClient'):
        cand = root + '/' + mod.replace('.', '/') + '.lean'
        if os.path.exists(cand): p = cand; break
    s = set()
    if p:
        txt = open(p).read()
        is_module = re.search(r'^module\s*$', txt, re.M) is not None
        for mt in re.finditer(r'^((?:public |meta |private )*)import (\S+)', txt, re.M):
            if (not is_module) or 'public' in mt.group(1):
                s.add(mt.group(2))
    mlpub[mod] = s
    return s
mlclo = {}
def ml_closure(mod):
    if mod in mlclo: return mlclo[mod]
    mlclo[mod] = set()
    s = set()
    for i in ml_pub(mod):
        s.add(i); s |= ml_closure(i)
    mlclo[mod] = s
    return s
def reduce_ml(mods):
    mods = set(mods)
    covered = set()
    for m in mods: covered |= ml_closure(m)
    return sorted(m for m in mods if m not in covered)

from fixups import FIXUPS
ROUTE_F = ['HasPolynomialType', 'HasBinaryType', 'monicDensity', 'projectiveDensity']

def transform(m, txt):
    txt = re.sub(r'SurfaceBlowupV2Orig\.(' + '|'.join(ROUTE_F) + r')\b', r'@@O_\1@@', txt)
    if m != 'Def_SurfaceBlowupV2_OrigDensity':
        txt = re.sub(r'\b(' + '|'.join(ROUTE_F) + r')\b', r'\1F', txt)
    txt = re.sub(r'@@O_(\w+)@@', r'SurfaceBlowup.\1', txt)
    txt = re.sub(r'\bSurfaceBlowupV2(Orig|Gen)?\b', 'SurfaceBlowup', txt)
    txt = re.sub(r'(?<![\w.])SolN(\w+)', r'SurfaceBlowup.SolN\1', txt)
    txt = re.sub(r'^set_option autoImplicit false\s*\n', '', txt, flags=re.M)
    # merged imports make Mathlib's 3-argument `Finset.mem_antidiagonal` (MulAntidiagonal) visible
    txt = re.sub(r'\bFinset\.(mem_)?antidiagonal\b', r'Finset.HasAntidiagonal.\1antidiagonal', txt)
    for pat, rep in FIXUPS.get(m, []):
        assert pat in txt, (m, pat)
        txt = txt.replace(pat, rep)
    return txt

def close_scopes(txt):
    stack = []
    for line in txt.split('\n'):
        if re.match(r'^(noncomputable\s+)?section\b', line):
            mt = re.match(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*(--.*)?$', line)
            stack.append(('s', mt.group(1) if mt else None))
        elif re.match(r'^namespace\s+\S+', line):
            stack.append(('n', line.split()[1]))
        elif re.match(r'^mutual\s*$', line):
            stack.append(('m', None))
        elif re.match(r'^end\b', line):
            if stack: stack.pop()
    closers = []
    for kind, name in reversed(stack):
        if kind == 'm': raise ValueError('unclosed mutual')
        closers.append('end' + (' ' + name if name else ''))
    return closers

out_mods = {}
modname = {}
for k, mod in enumerate(modules):
    nm = NAMES[mod['files'][0]]
    modname[k] = 'SurfaceBlowup.' + nm.replace('/', '.')
fmod = {f: k for k, mod in enumerate(modules) for f in mod['files']}

for k, mod in enumerate(modules):
    files = mod['files']
    ml = set()
    pj = set()
    for f in files:
        ml |= mathlib_closure(f)
        for d in deps.get(f, ()):
            if fmod[d] != k: pj.add(fmod[d])
    # transitive reduction of project imports
    def pclo(j, seen=None):
        return pjclo[j]
    out_mods[k] = (files, ml, pj)

# project-module closure for reduction
pjdeps = {k: v[2] for k, v in out_mods.items()}
pjclo = {}
for k in range(len(modules)):
    s = set(); stack = list(pjdeps[k])
    while stack:
        j = stack.pop()
        if j in s: continue
        s.add(j); stack += list(pjdeps[j])
    pjclo[k] = s

stats = []
for k, (files, ml, pj) in out_mods.items():
    pj_red = sorted(j for j in pj if not any(j in pjclo[i] for i in pj if i != j))
    # Mathlib imports already provided by imported project modules need not be repeated
    provided = set()
    for j in pjclo[k]:
        provided |= out_mods[j][1]
    ml_need = ml - provided
    covered = set()
    for x in provided: covered |= ml_closure(x) | {x}
    ml_need = reduce_ml(m for m in ml_need if m not in covered)
    hdr = [f'import {modname[j]}' for j in sorted(pj_red, key=lambda j: modname[j])]
    hdr += [f'import {x}' for x in ml_need]
    title = NAMES[files[0]].split('/')[-1]
    doc = ['', '/-!', f'# {title}', '', 'Mechanically unified from the certified `monolith_gen` nodes listed below (cycle 1);',
           'each node keeps its own `section`. Golfing is tracked in `CAPTAIN.md`.', '',
           '## Nodes', ''] + [f'* `{f}`' for f in files] + ['-/', '']
    parts = []
    for f in files:
        b = transform(f, body[f]).strip('\n')
        closers = close_scopes(b)
        slug = f.replace('Thm_SurfaceBlowupV2_', '').replace('Def_SurfaceBlowupV2_', 'Def ').replace('Thm_Gen_', 'Gen ')
        parts.append(f'/-! ### {slug} -/\n\nsection\n\n{b}\n' + ''.join(c + '\n' for c in closers) + '\nend\n')
    text = '\n'.join(hdr) + '\n' + '\n'.join(doc) + '\n' + '\n'.join(parts)
    p = DST + '/' + modname[k].replace('.', '/') + '.lean'
    os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, 'w').write(text)
    stats.append((modname[k], len(files), text.count('\n')))
json.dump({'modname': modname, 'fmod': {f: modname[k] for f, k in fmod.items()}}, open(DST + '/logs/modmap.json', 'w'), indent=1)
for s in sorted(stats): print(*s)
print('total lines', sum(s[2] for s in stats))
