#!/usr/bin/env python3
"""Generator of the allocator-generic proofs of deflate.c and inflate.c (src/proof/za/).

The specifications of src/proof/deflate and src/proof/inflate* fix strm->zalloc = zcalloc, strm->zfree = zcfree,
strm->opaque = Z_NULL and malloc tokens for zlib's blocks; these values sit inside the stream representations
that every body proof states (strm_at, strm_rep, the loop states).  The short laws res_free_* / res_memory_* give
zlib their own allocator, so the same proofs are needed with those values generic: a caller-supplied allocator
`ZA : zallocator` (src/proof/zutil/ZAlloc.v).

The script ports, declaration by declaration, what depends on these values:
- a configuration docs/port-za/cfg_<side>.py gives the target modules, text substitutions (SUBST: regexes
  applied to every declaration of the ported modules) and per-declaration patches (PATCHES: exact
  replacements, each of which must apply once);
- a declaration (a definition, a lemma with its proof, a user section, an Ltac, a notation...) is TAINTED when
  a substitution or a patch changes it, or when it mentions a tainted name; untainted declarations are not
  copied: the ported module `Require Export`s its original and uses them from there;
- each tainted name gets the suffix _za (so original and port never clash), each module with a tainted
  declaration is written to src/proof/za/<dir>/<file>.v (module Zlib.proof.za.<dir>.<file>), and the
  tainted declarations sit in `Section ZAlloc. Context {ZA : zallocator}. ... End ZAlloc.`, so that each one
  that mentions the allocator is generalised over it; commands with global effect (Ltac, hints, notations,
  local instances, Requires, scopes) are kept outside the section, which is closed and reopened around them.

The same machinery serves other ports: a configuration may set SUFFIX (default _za), OUT (the subdirectory of
src/proof/ and of the module path, default za), SECTION (the pair of texts opening and closing the section of
the tainted declarations, or None for no section), REQUIRES (what each ported module imports after its
original, default ZAlloc), STEM (a prefix of the ported files' stems, default none), WHAT (the header's
description of the port) and DROP ({module: [names]}: tainted declarations left out of the port, for lemmas that
cannot hold of the ported definitions and that the targets do not need).

Another directory of docs/ with configurations of its own (docs/port-hl/) runs this script through a wrapper that
sets HERE, the directory of the configurations, which the generated files name in their headers.

Usage (from the repository root):  python3 docs/port-za/port.py <side> [--check] [--list]
  --check: only compare with the files on disk (exit 1 if one differs); --list: print the tainted names.
"""
import glob
import importlib.util
import os
import re
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
HERE = os.path.dirname(os.path.abspath(__file__))   # the directory of the configurations cfg_<side>.py
SUFFIX = '_za'
STEM = ''
OPEN = '\nSection ZAlloc.\nContext {ZA : Zlib.proof.zutil.ZAlloc.zallocator}.\n'
CLOSE = '\nEnd ZAlloc.\n'


def load_cfg(side):
    path = os.path.join(HERE, 'cfg_%s.py' % side)
    spec = importlib.util.spec_from_file_location('cfg_' + side, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ----------------------------------------------------------------------------------------------------------
# text

def strip_comments_strings(t):
    """The text without comments and string literals (strings become "")."""
    out, i, depth, n = [], 0, 0, len(t)
    while i < n:
        if t.startswith('(*', i):
            depth += 1; i += 2; continue
        if depth:
            if t.startswith('*)', i):
                depth -= 1; i += 2; continue
            i += 1; continue
        if t[i] == '"':
            j = i + 1
            while j < n:
                if t[j] == '"':
                    if j + 1 < n and t[j + 1] == '"':
                        j += 2; continue
                    break
                j += 1
            out.append('""'); i = j + 1; continue
        out.append(t[i]); i += 1
    return ''.join(out)


def sentences(t):
    """Split Coq source into sentences, each with its leading whitespace and comments."""
    res, i, start, depth, n = [], 0, 0, 0, len(t)
    while i < n:
        c = t[i]
        if t.startswith('(*', i):
            depth += 1; i += 2; continue
        if depth:
            if t.startswith('*)', i):
                depth -= 1; i += 2; continue
            i += 1; continue
        if c == '"':
            i += 1
            while i < n:
                if t[i] == '"':
                    if i + 1 < n and t[i + 1] == '"':
                        i += 2; continue
                    break
                i += 1
            i += 1; continue
        if c == '.' and (i + 1 == n or t[i + 1].isspace()) and not (i > 0 and t[i - 1] == '.'):
            res.append(t[start:i + 1]); start = i + 1
        i += 1
    tail = t[start:]
    return res, tail


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
MODIFIERS = {'Local', 'Global', 'Program', 'Polymorphic', 'Monomorphic', 'Private', 'Export'}
PROOF_KW = {'Lemma', 'Theorem', 'Corollary', 'Fact', 'Remark', 'Proposition', 'Example'}
DEF_KW = {'Definition', 'Fixpoint', 'CoFixpoint', 'Let', 'Function'}
TYPE_KW = {'Inductive', 'CoInductive', 'Record', 'Structure', 'Variant', 'Class'}
END_KW = {'Qed', 'Defined', 'Admitted', 'Abort', 'Save'}


def words(s):
    s = strip_comments_strings(s).strip()
    attrs = re.match(r'^((?:#\[[^\]]*\]\s*)*)', s).group(1)
    s = s[len(attrs):]
    w = s.split()
    mods = []
    while w and w[0] in MODIFIERS:
        mods.append(w[0]); w = w[1:]
    return attrs, mods, w


class Unit:
    """A declaration or a command: kind 'decl' (goes inside the section when tainted), 'cmd' (always kept,
    outside the section), 'local' (a local instance or Ltac: kept outside, renamed when tainted)."""
    def __init__(self, kind, text, names):
        self.kind, self.text, self.names = kind, text, names
        self.tainted = False


def defined_names(sent):
    attrs, mods, w = words(sent)
    if not w:
        return []
    kw = w[0]
    body = strip_comments_strings(sent)
    names = []
    if len(w) > 1:
        names.append(re.match(r"[A-Za-z_][A-Za-z0-9_']*", w[1]).group(0) if re.match(r"[A-Za-z_]", w[1]) else None)
    if kw in TYPE_KW:
        # constructors and fields
        if ':=' in body:
            rhs = body.split(':=', 1)[1]
            if kw not in ('Record', 'Structure', 'Class'):
                # constructors (a record's `|` are inside its fields' matches)
                for c in re.findall(r"(?:^|\|)\s*([A-Za-z_][A-Za-z0-9_']*)", rhs):
                    names.append(c)
            m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_']*)?\s*\{(.*)\}", rhs, re.S)
            if m:
                if m.group(1):
                    names.append(m.group(1))
                for f in re.findall(r"(?:^|;)\s*([A-Za-z_][A-Za-z0-9_']*)\s*:", m.group(2)):
                    names.append(f)
    if kw in ('Fixpoint', 'CoFixpoint'):
        # mutual fixpoints: `with name` at the start of a line
        for extra in re.findall(r"(?m)^\s*with\s+([A-Za-z_][A-Za-z0-9_']*)", body):
            names.append(extra)
    return [n for n in names if n]


def units(text):
    sents, tail = sentences(text)
    us, i = [], 0
    while i < len(sents):
        s = sents[i]
        attrs, mods, w = words(s)
        kw = w[0].rstrip('.') if w else ''
        body = strip_comments_strings(s)
        if kw == 'Section':
            # a user section: one declaration up to its End
            name = w[1].rstrip('.')
            j, depth = i + 1, 1
            while j < len(sents) and depth:
                _, _, w2 = words(sents[j])
                k2 = w2[0].rstrip('.') if w2 else ''
                if k2 == 'Section':
                    depth += 1
                elif k2 == 'End':
                    depth -= 1
                j += 1
            txt = ''.join(sents[i:j])
            names = []
            for s2 in sents[i + 1:j]:
                a2, m2, w2 = words(s2)
                k2 = w2[0] if w2 else ''
                if k2 in PROOF_KW or k2 in DEF_KW or k2 in TYPE_KW or k2 in ('Instance',):
                    names += defined_names(s2)
            us.append(Unit('decl', txt, names)); i = j; continue
        proofy = (kw in PROOF_KW or ((kw in DEF_KW or kw == 'Instance') and ':=' not in body)
                  or kw == 'Goal' or (kw in ('Next',)))
        j = i + 1
        if proofy:
            while j < len(sents):
                _, _, w2 = words(sents[j])
                k2 = w2[0].rstrip('.') if w2 else ''
                j += 1
                if k2 in END_KW:
                    break
        txt = ''.join(sents[i:j])
        local = '#[local]' in attrs or 'Local' in mods
        if kw in PROOF_KW or kw in DEF_KW or kw in TYPE_KW:
            us.append(Unit('decl', txt, defined_names(s)))
        elif kw == 'Instance':
            us.append(Unit('local' if local else 'decl', txt, defined_names(s)))
        elif kw in ('Ltac', 'Ltac2'):
            nm = re.match(r"[A-Za-z_][A-Za-z0-9_']*", w[1]).group(0)
            us.append(Unit('local', txt, [nm]))
        else:
            us.append(Unit('cmd', txt, []))
        i = j
    if tail.strip():
        us.append(Unit('cmd', tail, []))
    elif tail:
        us.append(Unit('cmd', tail, []))
    return us


# ----------------------------------------------------------------------------------------------------------
# modules

def all_modules():
    mods = {}
    for f in glob.glob(os.path.join(ROOT, 'src', '**', '*.v'), recursive=True):
        rel = os.path.relpath(f, os.path.join(ROOT, 'src'))
        if rel.startswith(os.path.join('proof', OUT) + os.sep):
            continue
        mods['Zlib.' + rel[:-2].replace(os.sep, '.')] = f
    return mods


def deps_of(path, mods):
    t = strip_comments_strings(open(path).read())
    ds = []
    for sent in re.split(r'\.\s', t):
        if re.search(r'\bRequire\b', sent):
            for x in re.findall(r'Zlib\.[\w.]+', sent):
                x = x.rstrip('.')
                if x in mods and x not in ds:
                    ds.append(x)
    return ds


def topo(cfg, mods):
    deps = {}
    order, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        deps[m] = deps_of(mods[m], mods)
        for d in deps[m]:
            visit(d)
        order.append(m)
    for t in cfg.TARGETS:
        visit(t)
    return order, deps


def new_name(m):
    """The ported module of m: under Zlib.proof.<OUT>, its file stem prefixed with STEM (so that no ported file
    has the stem of another module)."""
    assert m.startswith('Zlib.proof.'), m
    parts = m[len('Zlib.proof.'):].split('.')
    return 'Zlib.proof.%s.' % OUT + '.'.join(parts[:-1] + [STEM + parts[-1]])


def configure(cfg):
    """The port's parameters: the configuration's, else the allocator port's."""
    global SUFFIX, OUT, OPEN, CLOSE, REQUIRES, WHAT, STEM
    STEM = getattr(cfg, 'STEM', '')
    SUFFIX = getattr(cfg, 'SUFFIX', SUFFIX)
    OUT = getattr(cfg, 'OUT', 'za')
    sec = getattr(cfg, 'SECTION', (OPEN, CLOSE))
    OPEN, CLOSE = sec if sec else ('', '')
    REQUIRES = getattr(cfg, 'REQUIRES', 'Require Import Zlib.proof.zutil.ZAlloc.\n')
    WHAT = getattr(cfg, 'WHAT', 'the\n   allocator values, with a caller-supplied allocator (src/proof/zutil/ZAlloc.v)')


def rename(text, tainted, ported, qualify=None):
    """Rename tainted names (bare or qualified) and the Requires of ported modules.  The bare names in `qualify`
    ({name: ported module}) are written fully qualified (their ported name is also an original one, which the
    Require Export of an original module would make the bare name mean)."""
    qualify = qualify or {}

    def sub_ident(mo):
        tok = mo.group(0)
        parts = tok.split('.')
        if tok in ported:
            return new_name(tok)
        last = parts[-1]
        if len(parts) == 1 and last in qualify:
            return new_name(qualify[last]) + '.' + last + SUFFIX
        if last in tainted:
            qual = '.'.join(parts[:-1])
            if qual:
                full = [m for m in ported if m == qual or m.endswith('.' + qual)]
                if full:
                    qual = new_name(full[0]) if qual.startswith('Zlib.') else qual
            return (qual + '.' if qual else '') + last + SUFFIX
        # a qualified name of an untainted declaration stays the original's (the port only re-exports it)
        return tok
    out, i, depth, n = [], 0, 0, len(text)
    # rename outside comments and strings only
    while i < n:
        if text.startswith('(*', i):
            j, d = i + 2, 1
            while j < n and d:
                if text.startswith('(*', j):
                    d += 1; j += 2
                elif text.startswith('*)', j):
                    d -= 1; j += 2
                else:
                    j += 1
            out.append(text[i:j]); i = j; continue
        if text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2; continue
                    break
                j += 1
            out.append(text[i:j + 1]); i = j + 1; continue
        mo = IDENT.match(text, i)
        if mo and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")):
            out.append(sub_ident(mo)); i = mo.end(); continue
        out.append(text[i]); i += 1
    return ''.join(out)


def mentions(text, names):
    for tok in IDENT.findall(strip_comments_strings(text)):
        if tok.split('.')[-1] in names:
            return True
    return False


def main():
    side = sys.argv[1]
    check = '--check' in sys.argv
    cfg = load_cfg(side)
    configure(cfg)
    mods = all_modules()
    order, deps = topo(cfg, mods)
    allowed = tuple(cfg.PREFIXES)
    candidates = [m for m in order if m.startswith(allowed)]
    tainted = set()
    defmod = {}
    per_mod = {}
    used_patches = set()
    for m in candidates:
        us = units(open(mods[m]).read())
        for u in us:
            orig = u.text
            t = orig
            for pat, rep in cfg.SUBST:
                t = re.sub(pat, rep, t)
            for k, (pm, old, new) in enumerate(cfg.PATCHES):
                if pm == m and old in t:
                    if t.count(old) != 1:
                        sys.exit('patch %d of %s applies %d times' % (k, m, t.count(old)))
                    t = t.replace(old, new); used_patches.add(k)
            u.text = t
            if u.kind != 'cmd' and (t != orig or mentions(t, tainted)):
                u.tainted = True
                tainted.update(u.names)
                for n in u.names:
                    defmod.setdefault(n, m)
            elif u.kind == 'cmd' and t != orig:
                u.tainted = True
        per_mod[m] = us
    for k, p in enumerate(cfg.PATCHES):
        if k not in used_patches:
            sys.exit('patch %d (%s) does not apply: %r' % (k, p[0], p[1][:80]))
    ported = [m for m in candidates if any(u.tainted for u in per_mod[m])]
    # a module that requires a ported module is ported too (its Requires change)
    changed = True
    while changed:
        changed = False
        for m in candidates:
            if m not in ported and any(d in ported for d in deps[m]):
                ported.append(m); changed = True
    ported_set = set(ported)
    # declarations left out of the port (a configuration's DROP: {module: [names]}), e.g. lemmas that cannot hold
    # of the ported definitions and that the targets do not need
    drop = getattr(cfg, 'DROP', {})
    # a tainted name whose ported name is an original name too is written qualified (outside its own module)
    # (only in the modules that see that original name: those that require its module)
    origmod = {}
    for m in candidates:
        for u in per_mod[m]:
            for n in u.names:
                origmod.setdefault(n, m)
    clash = {n: defmod[n] for n in tainted if n + SUFFIX in origmod and n in defmod}

    def sees(m, d, seen=None):
        seen = set() if seen is None else seen
        if m == d:
            return True
        seen.add(m)
        return any(sees(x, d, seen) for x in deps.get(m, []) if x not in seen)
    bad = 0
    for m in candidates:
        if m not in ported_set:
            continue
        us = per_mod[m]
        here = os.path.relpath(HERE, ROOT)
        out = ['(* Generated by %s/port.py from %s: its declarations that depend on %s and the suffix %s;\n'
               '   the others are the original ones (Require Export).  Do not edit: change the configuration\n'
               '   %s/cfg_%s.py and run the generator. *)\n'
               % (here, os.path.relpath(mods[m], ROOT), WHAT, SUFFIX, here, side)]
        inside = False
        exported = False
        for u in us:
            txt = rename(u.text, tainted, ported_set,
                         {n: d for n, d in clash.items() if d != m and sees(m, origmod[n + SUFFIX])})
            if u.kind == 'cmd':
                if not exported and not re.search(r'\bRequire\b', strip_comments_strings(u.text)) and \
                        strip_comments_strings(u.text).strip():
                    if inside:
                        out.append(CLOSE); inside = False
                    out.append('\nRequire Export %s.\n%s' % (m, REQUIRES))
                    exported = True
                if inside and strip_comments_strings(u.text).strip():
                    out.append(CLOSE); inside = False
                out.append(txt); continue
            if not exported:
                out.append('\nRequire Export %s.\n%s' % (m, REQUIRES))
                exported = True
            if u.kind == 'local':
                if inside:
                    out.append(CLOSE); inside = False
                out.append(txt); continue
            if not u.tainted or any(n in drop.get(m, ()) for n in u.names):
                continue
            if not inside:
                out.append(OPEN); inside = True
            out.append(txt)
        if inside:
            out.append(CLOSE)
        if not exported:
            out.append('\nRequire Export %s.\n%s' % (m, REQUIRES))
        txt = ''.join(out)
        if not txt.endswith('\n'):
            txt += '\n'
        dst = os.path.join(ROOT, 'src', *new_name(m).split('.')[1:]) + '.v'
        if check:
            if not os.path.exists(dst) or open(dst).read() != txt:
                print('differs:', dst); bad += 1
            continue
        if os.path.exists(dst) and open(dst).read() == txt:
            continue  # unchanged: keep its time stamp (the compiled modules that depend on it stay fresh)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(dst, 'w') as f:
            f.write(txt)
    print('%d modules %s, %d tainted names' % (len(ported), 'checked' if check else 'written', len(tainted)))
    if '--list' in sys.argv:
        for m in candidates:
            if m in ported_set:
                print(m, [n for u in per_mod[m] if u.tainted for n in u.names])
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
