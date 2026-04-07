You are solving a **Constrained Horn Clause (CHC)** problem over **algebraic data types (ADTs)** and integer arithmetic. I want a **catamorphism-based solution** in the spirit of Katsura et al., *Automated Catamorphism Synthesis for Solving Constrained Horn Clauses over Algebraic Data Types*.

Your task is to analyze the given SMT-LIB HORN instance and do the following.

## What to produce

1. Decide whether the CHCs are **SAT** or **UNSAT**.
2. If **SAT**, produce:
   - an **intuitive / intended model** for the predicates if possible,
   - a suitable **catamorphism** from each relevant ADT to integers or tuples of integers,
   - the corresponding **range / admissibility predicate** for the image of the catamorphism,
   - an **abstract integer-domain model** for the predicates after applying the catamorphism,
   - the induced **original ADT-domain model** obtained by lifting back through the catamorphism.
3. If **UNSAT**, explain the contradiction in the **original CHCs**, not only in the abstraction.

---

## High-level overview of the paper's approach / pipeline

The core problem is that CHCs over ADTs often require models that are naturally stated using inductive functions such as list length, list sum, alternating sum, or numeric value of Peano naturals. Standard CHC solvers are often much better at solving CHCs over **integers** than over ADTs directly.

The paper's key idea is therefore:

1. **Choose a catamorphism** `C` from the ADT to integers or tuples of integers.
   - A catamorphism is a fold-like summary map defined by one structure map per constructor.
   - Example patterns:
     - `Nat`: `Z -> 0`, `S(x) -> x + 1`
     - `List`: `nil -> 0`, `cons(x,l) -> 1 + l` (length)
     - `List`: `nil -> 0`, `cons(x,l) -> x + l` (sum)
     - `List`: `nil -> 0`, `cons(x,l) -> x - l` (alternating sum)
     - tuple-valued folds when one scalar is insufficient.

2. **Augment the original CHCs with an admissibility predicate** `P_delta` for each ADT sort.
   - This predicate represents "being in the image / being a valid abstractable value".
   - This matters because abstraction without range restrictions is often too coarse and can introduce spurious counterexamples.
   - In the abstract system, every universally quantified ADT variable is replaced by an integer variable together with a condition such as `P_delta(x)`.

3. **Abstract the CHCs into integer CHCs** by replacing each constructor application with the corresponding structure map of the catamorphism.
   - ADT equality is abstracted soundly by equality of catamorphism images.
   - The result is a CHC system over integer arithmetic, often much easier to solve.

4. **Solve the abstract CHCs**.
   - If the abstract system is SAT, then by soundness the original CHCs are SAT.
   - A model for the original predicates can be obtained by composing the abstract model with the catamorphism.

5. **If the abstract system is UNSAT**, check whether the UNSAT proof corresponds to a real contradiction in the original CHCs.
   - Extract a candidate counterexample / proof obligation from the abstract UNSAT derivation.
   - If that counterexample is genuinely satisfiable in the original ADT world, conclude **UNSAT**.
   - Otherwise it is **spurious**, meaning the current catamorphism was too weak.

6. **Refine the catamorphism**.
   - Search for a better catamorphism using templates, usually linear or affine folds first.
   - The paper uses a **counterexample-guided template synthesis** loop:
     - abstract,
     - solve,
     - extract spurious counterexample if needed,
     - strengthen the catamorphism so the same spurious proof becomes impossible,
     - repeat.

7. **Prefer simple catamorphisms first**, then richer tuple-valued ones if needed.
   - The paper uses a sequence of templates of increasing expressiveness.
   - In practice, many examples are solved by a small scalar or 2D/3D fold.

In short, the pipeline is:

**guess / synthesize fold -> add range predicate -> abstract to integer CHCs -> solve -> if spurious UNSAT, refine fold -> otherwise lift model back**.

---

## Key ideas you should actively use while solving

Follow the methodology below, not just generic CHC reasoning.

### A. First infer the semantic role of each predicate

Try to understand what each predicate is tracking:
- arithmetic relation between arguments,
- structural size,
- length of a list,
- sum of elements,
- alternating sum,
- parity,
- relation between two accumulators,
- generated family of ADT values,
- safety property in the final `false` clause.

Many CHC predicates correspond to a fold-derived invariant.

### B. Prefer simple folds first

Start with simple, interpretable catamorphisms:
- natural numbers -> numeric value / size,
- lists -> length,
- lists -> sum,
- lists -> alternating sum,
- tuples such as `(length, sum)`, `(sum_even_minus_odd, length)`, etc.

If one scalar summary is not enough, try a **tuple-valued catamorphism**.

### C. Use linear / affine templates first

A very common successful pattern is a linear catamorphism:
- `C(nil) = d`
- `C(cons(x,l)) = a*C(l) + b*x + c`

or tuple combinations of these.

For naturals:
- `C(Z) = a`
- `C(S(n)) = b*C(n) + c`

Try low-complexity coefficients first.

### D. Always think about the range predicate

Do **not** forget the image restriction / admissibility predicate.

Without it, the abstraction may be too coarse and may yield false contradictions or incorrect arithmetic states that no concrete ADT term can realize.

When the image is all integers, the range predicate may simplify to `true`; when the image is restricted, spell that out explicitly.

### E. Clause-by-clause validation matters

Once you propose a catamorphism and abstract model, check **every Horn clause** carefully.

For SAT cases, verify that each abstract clause is satisfied by your abstract predicate definitions.

For UNSAT cases, identify the concrete contradiction in the original clauses.

### F. Lift the abstract model back explicitly

If the abstract model defines e.g.
- `P_abs(u,v,w) := u + v = w`

and the ADT arguments are abstracted by `C`, then the original model should be written as
- `P(x,y,z) := P_abs(C(x), C(y), C(z))`

or equivalently with `C(x), C(y), ...` substituted directly.

---

## Heuristics that often work on these tasks

Use these aggressively.

- For Peano naturals, the right catamorphism is often simply the numeric value / size.
- For list-processing CHCs, the hidden invariant is often one of:
  - length,
  - sum,
  - alternating sum,
  - parity,
  - max/min (using `(ite cond e1 e2)`)
  - nth (using `ite`)
  - a pair/triple of such measures.
- Generator predicates often characterize a family of ADTs with a very simple abstract image.
- Safety clauses often directly reveal the needed invariant:
  - `false <- ...` frequently says exactly what arithmetic relation must hold.
- Equality on ADTs becomes equality of summaries only as a **sound abstraction**; do not silently treat it as full equivalence.

---

## Important requirement: output the catamorphism in Catalia-readable format

When you present the catamorphism, you MUST wrap it between the markers `<<START-CATA>>` and `<<END-CATA>>`.

### Catamorphism example 1

<<START-CATA>>
(
  ;; Bool_265 |-> (0/1)
  ( "Bool_265"
    ( "false_265"
      ( ()
        0
      )
    )
    ( "true_265"
      ( ()
        1
      )
    )
  )

  ;; list_194 |-> (ok, first, emp)
  ( "list_194"
    ( "cons_194"
      ( (x ok first emp)
        (* ok (ite (= emp 1) 1 (ite (<= x first) 1 0)))
        x
        0
      )
    )
    ( "nil_220"
      ( ()
        1
        0
        1
      )
    )
  )

  ;; pair_82 |-> (b, ok, first, emp)
  ( "pair_82"
    ( "pair_83"
      ( (b ok first emp)
        b
        ok
        first
        emp
      )
    )
  )
)
<<END-CATA>>

### Catamorphism example 2

<<START-CATA>>
(
  ( "Nat_0"
    ( "S_0"
      ( (x)
        (+ x 1)
      )
    )
    ( "Z_0"
      ( ()
        0
      )
    )
  )

  ;; list_0 |-> int (length)
  ( "list_0"
    ( "cons_0"
      ( (x y)
        (+ y 1)
      )
    )
    ( "nil_0"
      ( ()
        0
      )
    )
  )
)
<<END-CATA>>

---

## Required output format

Use exactly this structure.

### 1. Verdict
State `SAT` or `UNSAT`.

### 2. High-level idea
Briefly explain the invariant and why a catamorphism is appropriate.

### 3. Chosen catamorphism
Define the catamorphism precisely for each constructor.
Include the **Catalia-style catamorphism block** wrapped in `<<START-CATA>>` / `<<END-CATA>>` markers.
If tuple-valued, clearly name each component.

### 4. Range / admissibility predicate
Define the image predicate `P_delta`.
If it simplifies to `true`, say so and justify briefly.

### 5. Abstract model
Give explicit definitions of the predicates in the abstract integer domain.

### 6. Clause check
Check each Horn clause against the abstract model.

### 7. Lifted original model
Translate the abstract model back to the original ADT domain via the catamorphism.

### 8. If UNSAT
If the verdict is `UNSAT`, explain the contradiction in the original CHCs.

---

## Additional instructions

- Be mathematically explicit.
- Do not give only intuition; give actual formulas.
- If one catamorphism fails, refine it rather than giving up.
- If the intended model is recursive but the non-recursive one is easier to verify, provide both.
- Prefer concise but rigorous reasoning.