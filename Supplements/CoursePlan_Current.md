# Course Plan: Introduction to Proofs with Lean 4

An undergraduate course for mathematics students, taught using Lean 4 and Mathlib.
This version distinguishes between:

- material already covered in the lecture sequence from `Lectures/L01.lean` through `Lectures/L21.lean`, and
- later stages that are still planned for this class but have not yet been covered and whose lecture files are still to be written.

The original draft correctly anticipated the long-term direction of the course, but the actual delivery order developed somewhat differently. In particular, the course begins with Lean and type-theoretic foundations, places functions after relations and quotients, inserts cardinality and classical witness-extraction before analysis, and currently stops after the Archimedean property and density of $\mathbb{Q}$ in $\mathbb{R}$.

---

## Course Status

### Already covered

Stages 1 through 9 have corresponding lecture files and reflect the actual course progression.

### Still planned, not yet covered

Stages 10 through 12 remain part of the intended course plan, but they have not yet been taught. Those lectures are still to be written, so the descriptions below should be read as forward-looking rather than retrospective.

---

## Revised Stage Map

| Stage | Lectures | Status | Topic |
|------|----------|--------|-------|
| 1 | L01-L04 | Covered | Lean foundations and propositional logic |
| 2 | L05-L06 | Covered | Quantifiers and predicates |
| 3 | L07-L09 | Covered | Induction and arithmetic on natural numbers |
| 4 | L10-L11 | Covered | Sets and the logic-set dictionary |
| 5 | L12-L13 | Covered | Relations, equivalence, and quotients |
| 6 | L14-L15 | Covered | Functions, image/preimage, inverses, choice |
| 7 | L16-L17 | Covered | Cardinality and countability |
| 8 | L18-L19 | Covered | Classical witness extraction and unique existence |
| 9 | L20-L21 | Covered | Number systems and first real-analysis tools |
| 10 | Future | Planned | Supremum and infimum |
| 11 | Future | Planned | Sequences and limits |
| 12 | Future | Planned | Topology of the real line |

---

## High-Level Corrections to the Original Draft

- The course does not start directly with propositional logic. It starts with type theory, proof terms, Lean syntax, equality, and the distinction between term mode and tactic mode.
- Quantifiers appear as a short focused stage after the initial logic block, rather than as a long independent unit.
- Relations and quotient constructions are treated before the systematic unit on functions.
- Cardinality comes before the real-number and analysis material.
- `Classical.choose`, `noncomputable` definitions, and unique existence form a distinct stage after cardinality.
- Stages 10 through 12 still belong in the course plan, but they should be marked as planned continuation rather than as already matched by existing lectures.

---

## Dependency Graph

```text
                    ┌──────────────────────────────┐
                    │  Stage 1                     │
                    │  Lean Foundations &          │
                    │  Propositional Logic         │
                    └──────────────┬───────────────┘
                                   │
                                   ▼
                    ┌──────────────────────────────┐
                    │  Stage 2                     │
                    │  Quantifiers &               │
                    │  Predicates                  │
                    └──────────────┬───────────────┘
                                   │
                      ┌────────────┴────────────┐
                      ▼                         ▼
      ┌──────────────────────────────┐  ┌──────────────────────────────┐
      │  Stage 3                     │  │  Stage 4                     │
      │  Induction & Arithmetic      │  │  Sets & the Logic-Set        │
      │  on Natural Numbers          │  │  Dictionary                  │
      └──────────────┬───────────────┘  └──────────────┬───────────────┘
                     │                                 │
                     │                                 ▼
                     │              ┌──────────────────────────────┐
                     │              │  Stage 5                     │
                     │              │  Relations, Equivalence,     │
                     │              │  and Quotients               │
                     │              └──────────────┬───────────────┘
                     │                             │
                     │                             ▼
                     │              ┌──────────────────────────────┐
                     │              │  Stage 6                     │
                     │              │  Functions, Image/Preimage,  │
                     │              │  Inverses, Choice            │
                     │              └──────────────┬───────────────┘
                     │                             │
                     │                             ▼
                     │              ┌──────────────────────────────┐
                     │              │  Stage 7                     │
                     │              │  Cardinality &               │
                     │              │  Countability                │
                     │              └──────────────┬───────────────┘
                     │                             │
                     │                             ▼
                     │              ┌──────────────────────────────┐
                     │              │  Stage 8                     │
                     │              │  Classical Witness           │
                     │              │  Extraction & Exists-Unique  │
                     │              └──────────────┬───────────────┘
                     │                             │
                     └──────────────┐              │
                                    ▼              ▼
                    ┌──────────────────────────────┐
                    │  Stage 9                     │
                    │  Number Systems & First      │
                    │  Real-Analysis Tools         │
                    └──────────────┬───────────────┘
                                   │
                                   ▼
                    ┌──────────────────────────────┐
                    │  Stage 10 (planned)          │
                    │  Supremum & Infimum          │
                    └──────────────┬───────────────┘
                                   │
                                   ▼
                    ┌──────────────────────────────┐
                    │  Stage 11 (planned)          │
                    │  Sequences & Limits          │
                    └──────────────┬───────────────┘
                                   │
                                   ▼
                    ┌──────────────────────────────┐
                    │  Stage 12 (planned)          │
                    │  Topology of the Real Line   │
                    └──────────────────────────────┘
```

### Key prerequisite edges

| From | To | Reason |
|------|----|--------|
| Stage 1 | Stage 2 | Quantifiers build on implication, negation, conjunction, and disjunction |
| Stage 2 | Stage 3 | Induction statements and arithmetic predicates are naturally quantified |
| Stage 2 | Stage 4 | Sets are treated as predicates, so quantified logic feeds directly into set reasoning |
| Stage 4 | Stage 5 | Relations are predicate-valued objects and subset/order examples come from set theory |
| Stage 5 | Stage 6 | Quotients motivate later function constructions and inverse-style arguments |
| Stage 4 | Stage 6 | Image and preimage are set-theoretic operations |
| Stage 6 | Stage 7 | Cardinality is expressed through injections, surjections, and bijections |
| Stage 7 | Stage 8 | Classical witness extraction becomes useful after existence-heavy bijection arguments |
| Stage 3 | Stage 9 | The number-system ladder extends the arithmetic already developed on $\mathbb{N}$ |
| Stage 7 | Stage 9 | Density arguments are contrasted with countability and uncountability results |
| Stage 9 | Stage 10 | Supremum and infimum continue the completeness material introduced for $\mathbb{R}$ |
| Stage 10 | Stage 11 | Sequence convergence theorems naturally depend on suprema and completeness |
| Stage 11 | Stage 12 | Topology on the real line is closely tied to limits, continuity, and sequential ideas |

---

## Stage 1 - Lean Foundations and Propositional Logic

### Actual lecture coverage: L01-L04

### Mathematical notions and terminology

- Type theory as the ambient language
- Propositions as types and proofs as terms
- Equality and reflexivity
- Implication, negation, conjunction, disjunction, and equivalence
- Term mode versus tactic mode
- True and False as propositions

### Lean tactics and tools introduced

| Tool | Role |
|------|------|
| `rfl` | Reflexivity and definitional equality |
| `#check`, `#eval`, `#print` | Basic inspection and experimentation |
| `intro` | Introduce hypotheses and bound variables |
| `exact` | Close a goal with an exact proof term |
| `apply` | Use a theorem or hypothesis whose conclusion matches the goal |
| `contradiction` | Close a goal from inconsistent hypotheses |
| `exfalso` | Change the goal to `False` |
| `dsimp` | Definitional simplification |
| `constructor` | Build conjunctions and equivalences componentwise |
| `left`, `right` | Choose a branch of a disjunction goal |
| `rintro` | Combined introduction and pattern matching |
| `obtain` | Extract data from conjunctions and disjunctions |

### Adjustment from the original plan

The opening stage is broader than plain propositional logic. It includes Lean syntax, type-theoretic foundations, and proof construction habits before the course settles into standard logical content.

---

## Stage 2 - Quantifiers and Predicates

### Actual lecture coverage: L05-L06

### Mathematical notions and terminology

- Universal and existential quantifiers
- Predicates on a domain
- Witnesses for existential statements
- Quantified arithmetic examples
- Even and odd as sample predicates

### Lean tactics and tools emphasized

| Tool | Role |
|------|------|
| `use` | Provide a witness for an existential goal |
| `obtain` | Extract a witness and its property from an existential hypothesis |
| `intro` | Handle universal quantifiers as functions |
| `linarith` | Solve linear arithmetic side goals arising in quantified statements |

### Adjustment from the original plan

Quantifiers occupy a shorter bridge stage than originally projected. They function mainly as preparation for induction, sets, and later formal definitions.

---

## Stage 3 - Induction and Arithmetic on Natural Numbers

### Actual lecture coverage: L07-L09

### Mathematical notions and terminology

- Induction on natural numbers
- Custom inductive types
- Recursive definitions
- Basic arithmetic identities
- Summation formulas
- Dependent types and theorem-library conventions

### Lean tactics and tools introduced or becoming standard

| Tool | Role |
|------|------|
| `cases` | Case split on inductive data |
| `induction'` | Structured induction on natural numbers and related data |
| `calc` | Present multi-step algebraic or arithmetic proofs cleanly |
| `congrArg` | Apply a function to both sides of an equality |
| `rw` | Rewrite using equalities |
| `ring` | Normalize ring expressions |
| `norm_num` | Prove concrete numerical statements |

### Adjustment from the original plan

This stage is still centered on natural numbers and induction, but the lectures also use it to teach proof organization for computational algebra and to preview dependent-type ideas.

---

## Stage 4 - Sets and the Logic-Set Dictionary

### Actual lecture coverage: L10-L11

### Mathematical notions and terminology

- Sets as predicates
- Membership, subset, union, intersection, complement
- Extensionality of sets
- Indexed unions and intersections
- Cartesian product and power set
- De Morgan laws for sets

### Lean tactics and tools introduced or emphasized

| Tool | Role |
|------|------|
| `ext` | Prove set equality by pointwise membership equivalence |
| `show` | Clarify the exact goal being proved |
| `change` | Replace the goal with a definitionally equal statement |
| `have` | Introduce useful intermediate claims |
| `suffices` | Replace a goal with a sufficient subgoal |
| `simp` | Reduce set-theoretic membership to logical formulas |
| `tauto` | Finish pure logical goals after set reduction |
| `push_neg` | Push negation through quantified and logical structure |

### Adjustment from the original plan

This stage closely matches the original intent, but the lectures make the logic-set correspondence more explicit and central than the original draft did.

---

## Stage 5 - Relations, Equivalence, and Quotients

### Actual lecture coverage: L12-L13

### Mathematical notions and terminology

- Binary relations and their basic properties
- Equivalence relations and congruence modulo $n$
- Partial orders, with subset as the main motivating example
- Quotient types and well-definedness
- Residue classes and modular arithmetic

### Lean tactics and tools introduced or emphasized

| Tool | Role |
|------|------|
| `unfold` | Expand definitions of relations and properties |
| `omega` | Solve linear arithmetic over naturals and integers |
| `Quotient.mk` | Construct quotient elements |
| `Quotient.sound` | Show equal quotient classes from the underlying relation |
| `Quotient.exact` | Recover the underlying relation from quotient equality |
| `Quotient.lift` | Define functions on quotient types |
| `Quotient.ind` | Prove properties by working with representatives |
| `congr` | Transport equalities through constructors and functions |

### Adjustment from the original plan

The original draft treated relations and quotients as separate consecutive stages. In the actual lectures they form one tightly connected block, with Lecture 13 moving directly from equivalence relations to quotient constructions.

---

## Stage 6 - Functions, Image/Preimage, and Inverses

### Actual lecture coverage: L14-L15

### Mathematical notions and terminology

- Injective, surjective, and bijective functions
- Composition and identity
- Range, image, and preimage
- Left and right inverses
- Axiom of choice in the form of selecting preimages

### Lean tactics and tools introduced or emphasized

| Tool | Role |
|------|------|
| `funext` | Prove equality of functions by pointwise equality |
| `choose` | Extract a choice function from a family of existential statements |
| `aesop` | Lightweight automation for routine goals |
| `exact?` | Search for a closing lemma in examples |

### Adjustment from the original plan

Functions appear later than in the original draft, after sets, relations, and quotients. This matches the lecture flow, where image and preimage rely on the prior set-theoretic infrastructure and inverse constructions build on existential reasoning.

---

## Stage 7 - Cardinality and Countability

### Actual lecture coverage: L16-L17

### Mathematical notions and terminology

- Equinumerous sets
- Countably infinite versus uncountable
- Explicit bijections such as $\mathbb{N} \leftrightarrow \mathbb{Z}$
- Cantor's diagonal argument
- Power-set growth
- Schroder-Bernstein theorem
- Cantor pairing function

### Lean tactics and tools introduced or emphasized

| Tool | Role |
|------|------|
| `native_decide` | Compute decidable examples directly |
| `refine` | Build structured proofs with placeholders |
| `by_contra` | Indirect reasoning in cardinality arguments |
| `nlinarith` | Nonlinear arithmetic in pairing-function proofs |

### Adjustment from the original plan

Cardinality is not delayed until after a broad functions-and-relations arc. It comes immediately after the function stage and before any real analysis, which reflects the current lecture sequence.

---

## Stage 8 - Cardinality and Countability (4 Lectures)

### Actual lecture coverage: L18-L19

### Mathematical notions and terminology

- Turning existential proofs into explicit functions
- Choice as a term-forming principle
- Unique existence
- Chosen witnesses and their properties
- Larger-proof scaffolding using sections and local notation

### Lean tactics and tools introduced or emphasized

| Tool | Role |
|------|------|
| `Classical.choose` | Extract a witness from an existential proof |
| `Classical.choose_spec` | Recover the property of the chosen witness |
| `noncomputable` | Mark definitions that use classical choice |
| `∃!` | Express and use unique existence |

### Adjustment from the original plan

This stage does not appear in the original twelve-stage structure as an independent block, but it is now a genuine part of the course. It serves as a bridge between abstract existence arguments and later construction-heavy mathematics.

---

## Stage 9 - Number Systems and First Real-Analysis Tools

### Actual lecture coverage: L20-L21

### Mathematical notions and terminology

- The number-system ladder $\mathbb{N} \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{R}$
- Semiring, ring, and field vocabulary
- Ordered fields and completeness as background properties of $\mathbb{R}$
- Absolute value and triangle-style estimates
- Archimedean property
- Floor function
- Density of $\mathbb{Q}$ in $\mathbb{R}$
- Interval notation

### Lean tactics and tools introduced or emphasized

| Tool | Role |
|------|------|
| `field_simp` | Clear denominators in field expressions |
| `positivity` | Prove positivity and nonnegativity goals |
| `push_cast` | Normalize coercions across number systems |
| `exact_mod_cast` | Transfer equalities and inequalities across casts |
| `nlinarith` | Nonlinear inequalities over ordered fields |
| `gcongr` | Monotonicity-based inequality transport |
| `Int.floor` | Floor-function API |
| `Set.Ioo`, `Set.Icc`, `Set.Ico`, `Set.Ioc` | Interval constructors |

### Adjustment from the original plan

The current course reaches the real numbers but has not yet entered the originally planned later stages on suprema, sequences, or topology. At present, the analysis block ends with Archimedean arguments, floor, density, and intervals.

---

## Planned Continuation

The following stages remain part of the intended course trajectory, but they are still prospective.

## Stage 10 - Supremum and Infimum

### Status

Planned, not yet covered.

### Intended mathematical notions and terminology

- Supremum and infimum
- Least upper bounds and greatest lower bounds
- Maximum versus supremum and minimum versus infimum
- Approximation properties of suprema
- Sets of real numbers bounded above or below

### Likely Lean and Mathlib focus

- `IsLUB`, `sSup`, `le_csSup`, `csSup_le`
- Witness extraction from completeness statements
- `linarith` and `calc` for epsilon-style order estimates

---

## Stage 11 - Sequences and Limits

### Status

Planned, not yet covered.

### Intended mathematical notions and terminology

- Sequences and subsequences
- Convergence and divergence
- The epsilon-$N$ definition of limit
- Monotone and bounded sequences
- Cauchy sequences and convergence theorems

### Likely Lean and Mathlib focus

- `specialize` and witness extraction for epsilon arguments
- `use max N1 N2` patterns in combined estimates
- `Filter.Tendsto` and metric-space formulations of convergence

---

## Stage 12 - Topology of the Real Line

### Status

Planned, not yet covered.

### Intended mathematical notions and terminology

- Open and closed sets
- Interior, closure, and boundary
- Compactness and connectedness on the real line
- Continuity and neighborhood language
- Heine-Borel and related real-line topology results

### Likely Lean and Mathlib focus

- `IsOpen`, `IsClosed`, `Continuous`
- Neighborhood and filter language
- Set-based and sequential formulations of topological ideas

---

## Tactic and Tool Introduction Timeline

This table records the order in which the lectures actually introduce major tactics, APIs, or proof tools.

| Lecture | New tools or newly central tools |
|--------|-----------------------------------|
| L01 | `rfl`, `#check`, `#eval`, `#print`, term-style proof expressions |
| L02 | `intro`, `exact`, `apply`, `contradiction`, `exfalso` |
| L03 | `dsimp`, `constructor` |
| L04 | `left`, `right`, `rintro`, `obtain` |
| L05 | `use`, `linarith` |
| L07 | `cases`, `induction'` |
| L09 | `calc`, `congrArg` |
| L10 | `ext`, `show`, `change`, `have`, `suffices`, `tauto` |
| L11 | `push_neg`; systematic `simp` use for set logic |
| L12 | `unfold`, `omega` |
| L13 | Quotient API and explicit `congr` usage |
| L14 | `funext` |
| L15 | `choose`, `aesop`, occasional `exact?` |
| L16 | `native_decide` |
| L17 | `refine`, heavier use of `by_contra` |
| L18 | `Classical.choose`, `Classical.choose_spec`, `noncomputable` |
| L19 | `∃!` as a recurring proof pattern |
| L20 | `field_simp`, `positivity`, `push_cast`, `exact_mod_cast`, `nlinarith`, `gcongr` |
| L21 | `Int.floor`, interval constructors |

---

## Summary

The original plan remains useful as a view of the course's long arc, but it needed two corrections.

First, the covered material had to be reordered so that it matches the lecture files already written. Second, the later analysis and topology stages had to remain in the document while being labeled clearly as planned continuation rather than completed content.

With that adjustment, the plan now reflects both the actual course progression so far and the intended direction of the remaining part of the class.
