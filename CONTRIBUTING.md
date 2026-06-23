# Contributing to McCarthy

Thanks for your interest. McCarthy is small on purpose and friendly to first-time
contributors — most of the interesting work lives in *untrusted* code where a
mistake costs you a failing test, never a soundness bug.

## The one rule that matters

**Do not change `src/kernel.lisp` unless your change is specifically about the
trusted kernel, and even then expect intense review.** The kernel is the entire
trust surface (see `ARCHITECTURE.md`). New logical content does **not** go in the
kernel — it is *derived* from the ten existing primitive rules in `logic.lisp`,
`rewrite.lisp`, etc. If you find yourself wanting a new primitive rule or a new
axiom to make something provable, that is almost always the wrong move; open an
issue and let's discuss.

Everything outside the kernel is fair game: a wrong tactic, rewrite, or search
heuristic can only fail to find a proof, so you can experiment freely.

## Build & test

The only dependency is SBCL. The repo fetches one via `nix-shell -p sbcl`, so on
a machine with Nix you need nothing else:

```sh
bin/test            # the full suite — must be green before and after your change
bin/mccarthy demo   # quick sanity check
```

If you have SBCL on your PATH already, you can load the system directly:

```sh
sbcl --load src/load.lisp --load src/cli.lisp --eval '(mccarthy::demo)'
```

## Where things go

| You want to…                                   | Edit            |
|------------------------------------------------|-----------------|
| add a derived inference rule (e.g. a connective)| `src/logic.lisp`|
| improve matching or rewriting                  | `src/rewrite.lisp` |
| make the prover find more / faster             | `src/prover.lisp` |
| change surface syntax / printing               | `src/prover.lisp` (parser), `src/logic.lisp` (`pp`) |
| add request types to the service              | `src/cli.lisp`  |

Add a test for anything you add — `tests/smoke-*.lisp` show the pattern (each
file is a plain script that exits non-zero on failure). New theorems the prover
should handle go in `tests/smoke-prover.lisp` or `tests/smoke-rewrite.lisp`.

## PR checklist (the ship-gate, per change)

- [ ] `bin/test` is green (52/52 today, plus your new tests).
- [ ] No change to `src/kernel.lisp` unless the PR is explicitly about the kernel.
- [ ] New capabilities have at least one **positive** test (it proves the thing)
      and, where it could over-fire, one **negative** test (it refuses a
      non-theorem). Soundness is the product; guard it.
- [ ] Public claims in docs match what the code actually does. No "v1.0",
      "production-grade", or "complete" language on a pre-1.0 prover.
- [ ] Commits are descriptive; no generated-by trailers.

## Good first issues

See `GOOD_FIRST_ISSUES.md` — each is scoped to one file with a pointer to where
to start and a difficulty tag.

## Style

Match the surrounding code: lowercase-hyphenated names, short helpers, comments
that explain *why*. Watch for symbol collisions — Common Lisp uppercases reader
symbols, so a helper named `inst` and a rule spelled `INST` are the same symbol.
The kernel rules are deliberately named `prim-*` to avoid exactly this trap.
