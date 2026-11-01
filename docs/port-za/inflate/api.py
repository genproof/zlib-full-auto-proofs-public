"""Patches of the inflate port (docs/port-za/cfg_inflate.py), part api: see docs/port-za/inflate/README.md.

The part's patches are split by function, one file each (docs/port-za/inflate/api_<name>.py: PATCHES), so that
the bodies can be ported independently: api_uw (updatewindow, inflate/BodyUw5), api_dict
(inflateSetDictionary, inflate_api/Body5_dict), api_init (inflateInit2_, inflate_api/Body5_init), api_end
(inflateEnd and the reset functions, inflate_api/Body5_end and Body5_reset)."""
import importlib.util as _ilu
import os as _os


def _sub(name):
    path = _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), 'api_' + name + '.py')
    spec = _ilu.spec_from_file_location('cfg_inflate_api_' + name, path)
    mod = _ilu.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.PATCHES


PATCHES = [
    # inflateStateCheck: strm->zalloc / zfree are the caller's allocator functions (za_funcs)
    ('Zlib.proof.inflate.BodySmall',
     """    assert (Ez: zfuncs gv = (func_ptr' (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS)) za_alloc *
       func_ptr' (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS)) za_free)%logic) by reflexivity.""",
     """    assert (Ez: zfuncs gv = (func_ptr' (@zalloc_spec Zlib.units.Inflate.CS ZA) za_alloc *
       func_ptr' (@zfree_spec Zlib.units.Inflate.CS ZA) za_free)%logic) by reflexivity."""),
]

for _n in ['uw', 'dict', 'init', 'end']:
    PATCHES += _sub(_n)
