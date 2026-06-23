# Roadmap

McCarthy is built bottom-up: no layer is added until the one beneath it is sound
and tested. Current state — **sound HOL kernel + derived natural deduction +
matcher/rewriting engine + autonomous prover + stateless service, 52/52 tests.**

## Shipped

- [x] Trusted 10-rule HOL kernel, opaque `thm`, adversarial soundness test.
- [x] Connectives `T /\ ==> !` by definitional extension + derived rules.
- [x] Conversion / β-reduction engine.
- [x] First-order matcher + rewriting engine (equational reasoning).
- [x] Autonomous prover: backward decomposition + forward saturation +
      synthesized instantiation + equational search.
- [x] Reflective fact registry (`learn`).
- [x] Stateless REPL service + CLI.

## Next

1. **Classical extension.** `\/`, `?`, `~`, `F` (the first three definitional and
   axiom-free; full classical reasoning adds choice + extensionality as clearly
   marked axioms). Brings excluded middle, existentials, proof by contradiction.
2. **Higher-order (Miller-pattern) matching** — rewriting under binders with
   schematic rules.
3. **Conditional + ordered rewriting** — a real `simp`.
4. **A learned policy at the search seam.** `solve`'s witness/equation ordering
   is already isolated; rank candidates with a learned model. This is the hook
   for the "neural search over a Lisp kernel" thesis.
5. **Autoformalization front-end** — natural-language statement → s-expr goal,
   handed to `prove-sexp`.
6. **Proof objects & replay** — emit the primitive-rule trace as data so proofs
   can be independently rechecked and shared (homoiconic proof terms).

## Non-goals (for now)

- Competing with mathlib on abstract pure mathematics — McCarthy leans toward
  executable/equational/computational content, the ACL2-flavored sweet spot.
- A surface syntax beyond s-expressions. The point is that everything is data.
