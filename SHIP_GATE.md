# Ship gate

The quality bar a release must clear **before** the repo is promoted and the
community is invited. Inviting contributors to a half-baked repo is worse than
not inviting them; this file is the gate that prevents that.

| # | Criterion | Status |
|---|-----------|--------|
| 1 | Builds and runs with zero dependencies beyond SBCL (`nix-shell -p sbcl`). | ✅ |
| 2 | One-command reproducible test (`bin/test`) is fully green. | ✅ 52/52 |
| 3 | Trust surface is a single, small, isolated file (`src/kernel.lisp`). | ✅ |
| 4 | Soundness is adversarially tested: a false theorem cannot be forged; the prover refuses non-theorems. | ✅ |
| 5 | The system does something genuinely useful end-to-end (proves real first-order + equational theorems from their statements and certifies them). | ✅ |
| 6 | Docs are honest: no "production-grade" / "v1.0" / "complete" language; the reflective bet is named as a *seam*, not a moat. | ✅ |
| 7 | Contributor on-ramp exists: `CONTRIBUTING.md`, `ARCHITECTURE.md`, `GOOD_FIRST_ISSUES.md`, scoped layout. | ✅ |
| 8 | License present (`AGPL-3.0-or-later`). | ✅ |

**Gate status: PASS.** The repo is invite-ready.

Public promotion (mirroring out, announcing, soliciting contributors) is a
separate, deliberate operator decision — not triggered by this gate alone. The
gate establishes *readiness*; it does not pull the trigger.
