# Architecture

McCarthy is an LCF-style theorem prover: a tiny **trusted kernel** defines what a
theorem *is*, and everything else is untrusted code that can only build theorems
by calling the kernel. Soundness therefore depends on exactly one file.

## The trust boundary

```
                 ┌─────────────────────────────────────────┐
   UNTRUSTED     │ cli.lisp     stateless REPL service       │
   (cannot       │ prover.lisp  parser, search, fact registry│
    cause        │ rewrite.lisp matcher + rewriting engine   │
    unsoundness) │ logic.lisp   connectives + derived rules  │
                 └─────────────────────────────────────────┘
                 ╔═══════════════════════════════════════════╗
   TRUSTED       ║ kernel.lisp                                ║
   (the whole    ║   • opaque  thm  type                     ║
    trust        ║   • 10 primitive inference rules          ║
    surface)     ║   • definitional extension                ║
                 ╚═══════════════════════════════════════════╝
```

A `thm` is a struct whose constructor (`%make-thm`) is **not exported**. The only
functions that call it are the ten primitive rules. So no matter how wrong a
tactic, a rewrite, or the search is, it can only ever *fail to find* a proof — it
can never fabricate one. To audit McCarthy's soundness you audit `kernel.lisp`
and nothing else (the De Bruijn criterion).

## The logic

Higher-order logic = simply-typed λ-calculus + equality, after Church/HOL.

* **Types**: type variables, or applications of type constructors (`bool`, `fun`,
  `ind`). Well-formedness is checked on construction.
* **Terms**: `Var`, `Const`, `Comb` (application), `Abs` (λ). Constructed only
  through smart constructors that enforce well-typedness (`mk-comb` rejects a
  type mismatch, etc.).
* **The one primitive constant** is `=` at generic type `A→A→bool`. Everything
  else — `T`, `/\`, `==>`, `!` — is introduced by **definitional extension**
  (`new-basic-definition`), which is conservative: it cannot make the logic
  inconsistent.

### The ten primitive rules (`kernel.lisp`)

`REFL  TRANS  MK_COMB  ABS  BETA  ASSUME  EQ_MP  DEDUCT_ANTISYM_RULE  INST  INST_TYPE`

(named `prim-refl` … `prim-inst-type` in code). These are exactly the HOL Light
primitive basis. The delicate parts are capture-avoiding term substitution
(`vsubst`) and type instantiation with bound-variable renaming (`inst-term`);
both are tested directly in `tests/smoke-kernel.lisp`.

## The derived layer (`logic.lisp`)

Builds, using only the ten rules:

* conversion combinators (`then-conv`, `depth-conv`, …) and β-reduction;
* the connectives by definition, and the natural-deduction rules over them —
  `TRUTH`, `CONJ`, `CONJUNCT1/2`, `MP`, `DISCH`, `UNDISCH`, `GEN`, `SPEC`, `SYM`.

If any derivation here is wrong, the corresponding theorem just won't build.

## The rewriting engine (`rewrite.lisp`)

* `term-match`: first-order matching with type instantiation. Only designated
  metavariables are flexible; all other variables (and all bound variables) are
  rigid. So `a = b` rewrites exactly `a`; `!x. f x = g x` rewrites every `f _`.
* `rewr-conv`: turns an equational theorem into a conversion that emits a real
  `|- tm = tm'`.
* `bounded-depth-conv`: terminating normalization.

## The search (`prover.lisp`)

`solve` is a depth-bounded prover combining:

* **backward decomposition** — `/\` → prove both; `==>` → assume & prove; `!` →
  generalize;
* **forward saturation** (`forward-close`) — grow the assumption set with
  conjunction splits, universal instantiations at *synthesized witnesses*, and
  modus-ponens consequences;
* **equational search** (`solve-by-rewriting`) — rewrite the goal with an
  oriented equation drawn from the assumptions and recurse.

Every branch returns a kernel theorem, so a found proof is certified by
construction. The move-ordering choices (which witness, which equation) are the
natural seam for a learned policy — see `ROADMAP.md`.

## The reflective seam (`*facts*` / `learn`)

Proved theorems can be folded back into the search as reusable lemmas. Because
everything is an s-expression, the prover manipulates its own derived knowledge
as ordinary data. This is the Lisp-native bet; it is deliberately small today.
