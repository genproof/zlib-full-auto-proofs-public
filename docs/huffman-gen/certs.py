#!/usr/bin/env python3
"""Generator of the linear-programming certificates of src/proof/huffman/: the definitions cert128 .. cert32768
of CertData.v (gen_cert.py), certd4096 .. certd32768 of CertD.v (gen_certd.py) and cert_table of Repair.v
(repair_cert.py).

Each certificate is a set of integer multipliers that a linear-programming solver found (the dual of a linear
program over the facts the proof states); Coq checks every one by computation, so a wrong certificate fails the
build.  This script solves the linear programs again and writes the definitions; the rest of the three files
is written by hand.  It needs numpy and scipy (scipy.optimize.linprog with HiGHS); the inputs of the search for
memLevel 1 and 2 (lit_bufsize 128 and 256) are taus_128.txt and taus_256.txt.

Usage (from the repository root):  python3 docs/huffman-gen/certs.py [--check]
  --check: only compare the definitions with those in the files (exit 1 if one differs).
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
HUFF = os.path.join(ROOT, 'src', 'proof', 'huffman')
sys.path.insert(0, HERE)
try:
    import numpy  # noqa: F401
    import scipy.optimize  # noqa: F401
except ImportError:
    sys.exit('certs.py: needs numpy and scipy (pip install numpy scipy)')
import gen_cert
import gen_certd
import repair_cert


def zl(xs):
    return '[' + '; '.join(str(x) for x in xs) + ']'


def cert_data():
    out = {}
    for ml in range(1, 10):
        L = 2 ** (ml + 6)
        s = 0 if L <= 2048 else 2
        if L == 128:
            taus, db = gen_cert.lastlist(os.path.join(HERE, 'taus_128.txt')), 75
        elif L == 256:
            taus, db = gen_cert.lastlist(os.path.join(HERE, 'taus_256.txt')), 100
        else:
            taus, db = [], 100
        out['cert%d' % L] = gen_cert.coq('cert%d' % L, gen_cert.make(L, s, taus, db, verbose=False))
    return out


def cert_d():
    return {'certd%d' % L: gen_certd.make(L) for L in (4096, 8192, 16384, 32768)}


def cert_table():
    lines = []
    for c in repair_cert.certs(75, 15):
        alts = '[' + '; '.join('(%d, %s)' % (m, zl(e)) for m, e in c['alts']) + ']'
        lines.append('  (%s, (%d, %s, %s, %s, %d, %s))' % (zl(c['d']), c['Q'], zl(c['alpha']), zl(c['beta']),
                                                          zl(c['gamma']), c['sigma'], alts))
    return {'cert_table': 'Definition cert_table : list (list Z * cert) := [\n' + ';\n'.join(lines) + '\n].\n'}


def place(path, defs, check):
    """Put each definition `Definition <name> ... .` of defs in place of the one of that name in the file (or, with
    check, compare).  Returns the names that differ."""
    text = open(path).read()
    bad = []
    for name, new in defs.items():
        m = re.search(r'^Definition %s : .*?\.\n' % re.escape(name), text, re.M | re.S)
        if not m:
            sys.exit('certs.py: no definition %s in %s' % (name, os.path.relpath(path, ROOT)))
        if m.group(0) != new:
            bad.append(name)
            text = text[:m.start()] + new + text[m.end():]
    if bad and not check:
        open(path, 'w').write(text)
    return bad


def main():
    check = '--check' in sys.argv[1:]
    rc = 0
    sys.stdout.flush()
    for f, defs in (('CertData.v', cert_data()), ('CertD.v', cert_d()), ('Repair.v', cert_table())):
        bad = place(os.path.join(HUFF, f), defs, check)
        print('src/proof/huffman/%s: %d definitions %s%s' % (f, len(defs), 'checked' if check else 'written',
                                                              ', differ: ' + ', '.join(bad) if bad else ', identical'))
        rc |= bool(bad) and check
    sys.exit(1 if rc else 0)


if __name__ == '__main__':
    main()
