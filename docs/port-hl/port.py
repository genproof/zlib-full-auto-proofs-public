#!/usr/bin/env python3
"""Generator of the ports of inflate()'s proofs for the round trip with a gzip header (src/proof/hl/, src/proof/hlza/, src/proof/hl9h/):
docs/port-za/port.py with the configurations of this directory, docs/port-hl/cfg_<side>.py (the generated files name
this directory in their headers).

Usage (from the repository root):  python3 docs/port-hl/port.py <side> [--check] [--list]
"""
import importlib.util
import os

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('port', os.path.join(HERE, '..', 'port-za', 'port.py'))
port = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(port)
port.HERE = HERE

if __name__ == '__main__':
    port.main()
