# McCarthy — the Aristotle of Lisp

**[Status](STATUS.md) · [Roadmap](ROADMAP.md) · [Contributing](CONTRIBUTING.md) · [Issues](https://github.com/SMC17/mccarthy/issues) · [Public roadmap](https://github.com/users/SMC17/projects/16)**

A self-contained, **sound** automated theorem prover whose trusted core is a
higher-order logic kernel written homoiconically in Common Lisp, with an
agentic proof-search layer on top. Named for John McCarthy.

It is the Lisp-substrate answer to Harmonic's *Aristotle* (a Lean-backed neural
prover): same recipe — **informal/agentic search on top, an inviolable formal
kernel underneath, a stateless REPL service as the interface** — but with the
kernel, the proof states, the tactics, and the search all living as
s-expressions, so the system can manipulate (and extend) its own machinery as
data.

```
$ bin/mccarthy demo
McCarthy — the Aristotle of Lisp.  Certified by a 10-primitive HOL kernel.

  request : (prove sig ((p bool) (q bool)) goal (==> (and p q) (and q p)))
  response: (theorem hyp nil concl (==> (/\ p q) (/\ q p)) certified-by kernel)
  ...
```

## What it actually does (no overclaiming)

* Implements **higher-order logic** (simply-typed λ-calculus + equality) in the
  LCF tradition: a tiny *trusted kernel* exposes an opaque `thm` type whose only
  constructors are **ten primitive inference rules**. Everything else is
  untrusted and cannot break soundness — a buggy tactic merely fails to produce
  the theorem it wanted.
* Derives the logical connectives `T  /\  ==>  !` by **definitional extension**
  (no new axioms) and the standard natural-deduction rules over them, purely
  from the ten primitives.
* Runs an **autonomous prover** that, given only the s-expression statement of a
  goal, finds and **kernel-certifies** proofs of real theorems — propositional
  and genuine first-order-with-quantifiers — and correctly **refuses
  non-theorems** (it never returns a false proof).
* Exposes a **stateless REPL service**: submit a request s-expression on stdin,
  receive a certified response s-expression on stdout.
* Supports **reflective self-extension**: any theorem it proves can be `learn`ed
  back into the fact base and reused in later searches.

Verified examples it proves from their statements alone (see `tests/`):

```
|- (p /\ q) ==> (q /\ p)
|- (p ==> q) ==> (q ==> r) ==> (p ==> r)
|- !x. x = x
|- (!x. P x) ==> P c
|- (!x. P x ==> Q x) ==> (!x. P x) ==> (!y. Q y)
|- (a = b) ==> (P a ==> P b)                 ; equational / Leibniz
|- (p \/ q) ==> (q \/ p)                      ; disjunction
|- (p ==> q) ==> (~q ==> ~p)                  ; contrapositive
|- ~(p /\ ~p)                                 ; non-contradiction
```

and rejects `p ==> q`, `(P c) ==> (!x. P x)`, `(p \/ q) ==> p`, and even
`p \/ ~p` — excluded middle is *not* provable in the axiom-free intuitionistic
core, and the prover is faithful to that rather than quietly assuming it.

## Why Lisp (the honest version)

Homoiconicity is **not** what makes a neural prover strong — data, search and
compute are. What it *does* buy, and what this codebase exploits, is that
**terms, proof states, tactics, derived facts and the search's own synthesized
steps are all the same kind of object: s-expressions.** That makes one thing
genuinely natural here that is awkward elsewhere: the prover **synthesizes new
inference steps as first-class data mid-search** (universal instantiation at
guessed witnesses, modus-ponens consequences, conjunction splits) and can fold
proved theorems back into its own search state. That reflective self-extension
seam is the real frontier bet — and it's marked as a seam, not a finished moat.

## Architecture — mapped to Aristotle

| Aristotle (Harmonic, Lean)            | McCarthy (this repo, Lisp)                          |
|---------------------------------------|-----------------------------------------------------|
| Lean 4 kernel (dependent types)       | `src/kernel.lisp` — 10-rule HOL kernel, opaque `thm`|
| mathlib + tactic language             | `src/logic.lisp` — connectives + derived rules      |
| MCGS / hypertree policy+value search  | `src/prover.lisp` — backward + forward saturation   |
| expert iteration / learned lemmas     | `*facts*` registry + `learn` (reflective seam)      |
| stateless Lean REPL service           | `src/cli.lisp` — `serve`: form in → certified form out |

The **trust boundary** is exactly one file: `src/kernel.lisp` (De Bruijn
criterion). Audit it and you have audited the soundness of every proof the
system will ever emit.

## Quickstart

Requires only an SBCL (the repo fetches one via `nix-shell -p sbcl`; no other
dependencies, no quicklisp).

```sh
bin/test            # run all three suites (kernel soundness, logic, prover)
bin/mccarthy demo   # built-in demonstration
bin/mccarthy serve < tests/requests.lisp   # stateless service over stdin
```

Request grammar:

```lisp
(prove :sig ((p bool) (q bool)) :goal (==> (and p q) (and q p)) :depth 14)
(learn :sig (...) :goal (...))   ; prove, then add to the fact base
(facts)                          ; list learned lemmas
(reset)                          ; clear the fact base
```

Connectives in the surface syntax: `=`, `and` / `/\`, `==>` / `imp`,
`or` / `\/`, `not` / `~`, `F` (falsity), `!` / `forall`
(binder: `(! (x type) body)`), `lam`. Types: `bool`, type variables (any other
symbol), `(fun a b)` / `(-> a b)`.

## Roadmap to genuine Aristotle-scale

This is a sound, working foundation — deliberately bottom-up. The honest next
layers, in order:

1. **Higher-order matching + a rewriting engine** (conversions are already in
   `logic.lisp`) → equational/computational mathematics, the ACL2-style sweet
   spot.
2. **Classical extension** (choice + extensionality axioms) for `\/`, `?`, `~`,
   excluded middle.
3. **A neural policy seam**: `solve` already isolates the move-ordering choice;
   drop a learned policy in to rank tactic/witness candidates.
4. **Autoformalization front-end**: English → s-expr goal.

## Layout

```
src/kernel.lisp   trusted HOL kernel (the entire trust surface)
src/logic.lisp    connectives + derived natural-deduction rules
src/prover.lisp   parser + autonomous search + reflective fact registry
src/cli.lisp      stateless REPL service + command line
src/load.lisp     loads the system in order
tests/            kernel / logic / prover suites
bin/              mccarthy (CLI) · test (suite runner) · sbcl-run
```

## License

AGPL-3.0-or-later.
