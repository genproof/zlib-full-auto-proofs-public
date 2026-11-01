#!/usr/bin/env python3
"""The generator of src/proof/dnull/ (deflate() with next_in = Z_NULL): docs/port-za/port.py with the configuration
docs/port-za/cfg_dnull.py, each ported module named after its original with the suffix _N (DSpec -> DSpec_N, module
Zlib.proof.dnull.deflate.DSpec_N), so that no ported file has the name of its original.

Usage (from the repository root):  python3 docs/port-za/port_dnull.py [--check] [--list]"""
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('port', os.path.join(HERE, 'port.py'))
port = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(port)

_new_name = port.new_name


def new_name(m):
    return _new_name(m) + '_N'


port.new_name = new_name

if __name__ == '__main__':
    sys.argv = [sys.argv[0], 'dnull'] + sys.argv[1:]
    port.main()
