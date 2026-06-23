# Roadmap

McCarthy is built bottom-up: no layer is added until the one beneath it is sound
and tested. Current state — **sound HOL kernel + derived natural deduction +
matcher/rewriting engine + intuitionistic connectives + autonomous prover +
stateless service, 64/64 tests.**

## Shipped

- [x] Trusted 10-rule HOL kernel, opaque `thm`, adversarial soundness test.
- [x] Connectives `T /\ ==> !` by definitional extension + derived rules.
- [x] Conversion / β-reduction engine.
- [x] First-order matcher + rewriting engine (equational reasoning).
- [x] Disjunction `\/`, negation `~`, falsity `F` — definitional, **axiom-free**,
      with `DISJ1/2`, `DISJ_CASES`, `NOT_ELIM/INTRO`, `CONTR`; the prover
      case-splits on disjunctive assumptions and discharges contradictions.
- [x] Autonomous prover: backward decomposition + forward saturation +
      synthesized instantiation + equational search + ex falso.
- [x] Reflective fact registry (`learn`).
- [x] Stateless REPL service + CLI.

## Next

1. **Existentials `?`** (definitional, axiom-free: `EXISTS` intro + `CHOOSE`
   elim) and **classical reasoning** (excluded middle / proof-by-contradiction
   via a clearly-marked choice or `EM` axiom — the first axioms in the system,
   isolated and labelled).
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
