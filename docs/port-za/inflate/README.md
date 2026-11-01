# The parts of the inflate port (docs/port-za/cfg_inflate.py)

`python3 docs/port-za/port.py inflate` writes src/proof/za/{inflate,inflate_api,inffast}/.  The patches of
the generated proofs are split by part, one file each; the interface patches (the definitions and
specifications, which the other parts use) are in cfg_inflate.py itself.

| file | modules (Zlib.proof.za.*) | target |
|---|---|---|
| cfg_inflate.py | the shared base, compiled and fixed once: inflate.{ZAV,ZEvents,ZTac (hand-written), Inv, Inv2, Inv3, Rep, Loop, Loop2, Callees, Callees3, Callees5, CaseCommon, CaseKit, CaseKit5, CaseHyps, CaseHyps5, Cover3, MwfLemmas, ModeKit}, inflate_api.{Spec5, Bodies5} | (interface) |
| inflate/kit.py, inflate/cases.py | every other module of src/proof/za/inflate/ except BodySmall, BodyUpdatewindow, BodyUw5 | inflate/CasesAllZ.v `za_cases_proof : za_cases_stmt` |
| inflate/fast.py | src/proof/za/inffast/* | inffast/FastZ.v `za_fast_proof : za_fast_stmt` |
| inflate/body.py | inflate_api.{Body5_inflate, Body5Parts, Body5Conv, Body5Pro, Body5Loop, Body5Exit, Body5ExitKit, Body5ExitTail, Body5ExitWin, Body5Fin, Body5StepHdr, Body5StepInv} | inflate_api/BodyZ.v `za_body_inflate_proof : za_body_inflate_stmt` |
| inflate/api.py | inflate.{BodySmall, BodyUpdatewindow, BodyUw5}, inflate_api.{Body5_init, Body5_reset, Body5_end, Body5_dict, ResetKit5, ResetSplit5} | inflate_api/ApiZ.v `za_api_proof : za_api_stmt` |

Statements: src/proof/za/inflate_api/Stmt.v (per allocator), USpec.v (one spec per function).
