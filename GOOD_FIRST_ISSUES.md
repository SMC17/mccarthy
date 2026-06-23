# Good first issues

Each task is scoped to (mostly) one file, has a difficulty tag, and includes a
starting pointer. Add tests with your change. None of these touch the trusted
kernel.

### easy

1. **`<=>` as surface sugar for boolean equality.**
   In `parse-term` (`src/prover.lisp`), make `(<=> a b)` parse to `mk-eq` (which
   at type `bool` already means iff). Add a printer case in `pp` (`logic.lisp`)
   so a `bool`-typed equation prints as `(<=> …)`. Tests in `smoke-logic.lisp`.

2. **Flatten application chains in the printer.**
   `pp` currently prints `(f a b)` as `((f a) b)`. Make curried applications
   print flat. File: `src/logic.lisp` (`pp`).

3. **A `:trace` option on `prove` requests.**
   In `handle-request` (`src/cli.lisp`), accept `:trace t` and include the
   number of primitive-rule applications in the response. (Add a counter to the
   kernel rules behind a special variable — this is the *one* allowed touch of
   `kernel.lisp`, additive and non-logical; discuss in the issue first.)

### medium

4. **η-conversion.** Add `eta-conv` (`(\x. f x) = f` when `x` not free in `f`)
   to the conversion library and a `beta-eta-rule`. File: `src/logic.lisp` /
   `src/rewrite.lisp`.

5. **Existential `?`, definitionally.** `\/`, `~`, `F` already shipped; add the
   existential the same way: `? = \P. !q. (!x. P x ==> q) ==> q`, with `EXISTS`
   (intro, at a synthesized witness) and `CHOOSE` (elim). **No axioms.** Then
   teach `solve` to introduce a witness for a `?` goal and to `CHOOSE` on an
   existential assumption. File: `src/logic.lisp`, `src/prover.lisp`. Targets:
   `(P c) ==> (?x. P x)`, `(?x. P x) ==> (!x. P x ==> q) ==> q`.

6. **A `simp`-style tactic** that uses the learned `*facts*` equations as a
   rewrite set to normalize goals before search. File: `src/prover.lisp`.

7. **Conditional rewriting**: allow rules of the form `|- h ==> (l = r)`, firing
   only when `h` is dischargeable by the prover. File: `src/rewrite.lisp` +
   `src/prover.lisp`.

### hard

8. **Higher-order pattern matching.** Extend `term-match` (`src/rewrite.lisp`)
   to Miller patterns: a metavariable applied to distinct bound variables,
   `?P x`, matching by abstraction. Unlocks rewriting under binders with
   schematic rules (e.g. `!P. (!x. P x) ==> P c`-style).

9. **A learned move-ordering policy.** `solve` picks witnesses and equations in
   a fixed order; factor that choice behind a ranking function so an external
   (even statistical) policy can be plugged in. File: `src/prover.lisp`.

If you pick one up, open an issue saying so, and ask anything — the maintainers
would rather answer early than review a wrong turn late.
