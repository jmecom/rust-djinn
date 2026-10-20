# Writing Djinn specifications

The human's main job in Djinn is to decide exactly what a function means.
The implementation agent chooses how to compute it. A proof can establish that
an implementation satisfies your constraints; it cannot establish that those
constraints describe the behavior you intended.

This workshop develops a specification for finding the first occurrence of a
value in a list. You will start from a requirement, discover an ambiguity,
and refine the constraints until they describe one result for every input.
Use the [language tour](LANGUAGE_TOUR.md) for individual syntax forms and
[onboarding](FIRST_STEPS.md) for the crate setup and implementation commands.

You can follow the reasoning without installing anything. To check the drafts,
you need the Djinn CLI and Z3 from [installation](INSTALL.md), but no coding
agent or Lean installation. Use the new-crate recipe in the onboarding guide,
replace `src/spec.rs` with each complete block below, and run the commands from
that crate's directory. Also replace `pub use spec::abs;` in `src/lib.rs` with
`pub use spec::first_index;`, keeping the existing `spec` and `solution` module
declarations. The drafts are alternatives, not functions to paste into the same
file together.

## 1. Decide the observable behavior

Start with a short requirement:

> Given a list of integers and a value to find, return the index of its first
> occurrence. Return no index if the value is absent.

Before writing constraints, make the requirement concrete:

| Input list | Value | Required result | Decision this records |
|---|---:|---|---|
| `[]` | `5` | `None` | Empty input is valid |
| `[5]` | `5` | `Some(0)` | Indices start at zero |
| `[3, 5, 5]` | `5` | `Some(1)` | Duplicates select the first occurrence |
| `[3, 5, 5]` | `4` | `None` | Absence is a normal result |
| `[-2, 7]` | `7` | `Some(1)` | A match at the final index is included |

These examples help review intent; they do not replace a specification over all
inputs. They already determine useful design choices. The list is borrowed and
unchanged, so use `&[i32]`. A Rust index is a `usize`. Since an index need not
exist, the result is `Option<usize>`. Every input is valid, so this function
needs no `#[requires]` clause.

An alternative API could require that the value occurs and return `usize`.
That would be a different contract: callers would have to establish membership
before calling it. Choose between those APIs based on the behavior callers
need, rather than adding a precondition merely to make a difficult case disappear.

## 2. Write down what must hold of an answer

First try the following deliberately incomplete draft:

```rust
use djinn::djinn;

djinn! {
    pub fn first_index(values: &[i32], needle: i32) -> out: Option<usize> {
        if needle in values {
            some i: usize {
                out == Some(i);
                i < values.len();
                for j in 0..values.len() {
                    j == i => values[j] == needle;
                }
            }
        } else {
            out == None;
        }
    }
}
```

Read it as a collection of claims. If the value occurs, there is an index `i`
within the list, the result is `Some(i)`, and the element at that index matches.
If the value is absent, the result is `None`. `some` introduces an existential
witness: it asserts that such an `i` exists. It does not instruct the
implementation to search for one in any particular way.

The `for` statement asserts a property at every input index `j`.
The implication `j == i => values[j] == needle` constrains the selected index.
Other indices impose no condition yet. Iterating over `0..values.len()` also
keeps every indexed access in bounds, including when the list is empty.

There is still a missing requirement. For `[3, 5, 5]` and `needle = 5`, both
`Some(1)` and `Some(2)` satisfy this draft. It specifies a matching occurrence,
without saying which occurrence to return.

## 3. Use a counterexample to find the missing requirement

Run:

```sh
cargo djinn smoke-test --only first_index
```

The draft produces an `AMBIGUOUS` unambiguity result. The exact counterexample
can vary, but it has repeated matching values and two allowed result indices.
Use that witness to ask which answer the requirement permits. Here only the
earlier match is correct, so the specification must exclude every earlier
matching position.

Add the second implication inside the loop:

```rust
use djinn::djinn;

djinn! {
    pub fn first_index(values: &[i32], needle: i32) -> out: Option<usize> {
        if needle in values {
            some i: usize {
                out == Some(i);
                i < values.len();
                for j in 0..values.len() {
                    j == i => values[j] == needle;
                    j < i => values[j] != needle;
                }
            }
        } else {
            out == None;
        }
    }
}
```

Each clause now has a specific role:

| Clause | What it establishes |
|---|---|
| `if needle in values` | Separate the presence and absence cases using the input |
| `some i: usize` and `out == Some(i)` | Relate the optional result to an index |
| `i < values.len()` | Require an index inside the list |
| `j == i => values[j] == needle` | The selected position actually matches |
| `j < i => values[j] != needle` | No earlier position matches |
| `out == None` in the other branch | Determine the result when no match exists |

Run the same smoke-test again. For this version, the consistency, existence,
unambiguity, and well-formedness checks find no counterexample within their
bounds. This is useful feedback, but it is not a proof for arbitrary inputs.

Notice that the branch tests the input, not `out.is_some()`. Djinn rejects
statement conditions that depend on the named output. Use input cases to
organize the specification, and write constraints on the result within them.

## 4. Explain existence and uniqueness to yourself

Before asking an agent for proofs, try a short argument in ordinary language.
It often exposes a gap more clearly than adding more syntax.

**Existence:** If `needle` is absent, `None` satisfies the second branch.
Otherwise the finite list has a first matching position. Its index is in bounds,
its element matches, and every earlier element differs. Returning that index
therefore satisfies the first branch.

**Uniqueness:** In the absent case, only `None` is allowed. In the present case,
suppose two different indices were allowed. The smaller one would be a match
before the larger one, contradicting the larger index's “no earlier match”
constraint. The indices, and therefore the results, must be equal.

This argument is an authoring check, not a machine-checked proof. It explains
why each requirement is needed and gives you a basis for reviewing a later
change. It also keeps implementation choices separate: the specification says
nothing about loops, early returns, vectorization, or the order of searching.

## 5. Try removing a clause

A useful review technique is to delete one constraint mentally and construct an
unwanted answer that would become legal. For this function:

| Removed requirement | An unwanted result that becomes possible |
|---|---|
| The match at the selected position | `[3, 5]`, `needle = 5`, returning `Some(0)` |
| No earlier match | `[5, 5]`, `needle = 5`, returning `Some(1)` |
| The entire `else` branch | `[]`, `needle = 5`, returning any `Option<usize>` |

The bounds clause is a useful example of redundancy. In the completed version,
membership and the no-earlier-match clause already force `i` into range: an
out-of-range `i` would place every matching element before it, contradicting
that clause. Keeping the explicit bound still makes the contract easier to read.

In the earlier draft, before adding the no-earlier-match clause, the bound is
essential. Without it, `[5]` and `needle = 5` could return `Some(1)`: the loop
never visits index 1, so its implication imposes no condition on that candidate.
Constraints quantified over an empty range likewise hold without imposing
anything. Check whether a selected index must exist in the domain you quantify
over, rather than assuming the quantifier establishes that fact.

Not every clause needs to be logically independent. A redundant assertion can
make intent easier to review. The point is to understand what guarantees each
clause supplies and which ones follow from the others.

## 6. Distinguish kinds of failure

Smoke testing looks for several different problems. A proof attempt can also
fail because the tools or agent cannot solve the obligation, so a failed proof
attempt alone does not establish that a specification is wrong.

| Finding | Author's next question | Typical repair |
|---|---|---|
| Ambiguity | Which of the two admitted answers did I intend? | Add a missing requirement, including tie-breaking or error behavior |
| Missing output | Should this input be valid, and can the result type express its answer? | Handle the case, widen the result type, or justify a precondition |
| Contradiction | Which requirements cannot hold together? | Correct the conflicting requirement; do not arbitrarily delete one |
| Ill-formed expression | Under what conditions is this operation meaningful? | Establish index bounds, nonzero divisors, or callee preconditions |
| Failed `ensures` | Does this claimed consequence actually follow from the body? | Repair the body or correct the claim |
| Unsupported, skipped, or timed out | What did the tool actually check? | Consult the supported syntax and report; do not treat this as success |

For a concrete contrast, `r >= 0; r == x || r == -x;` describes the absolute
value of an `i32` input when `r` is an `i64`. Using `i32` for the output makes
`x = i32::MIN` impossible: its positive magnitude is too large. Adding
`r < 0` to the original body instead makes the constraints contradictory for
every input. An output-domain problem and conflicting requirements need
different repairs.

The [onboarding guide](FIRST_STEPS.md) works through this absolute-value example.
The [broken examples](../example/broken/README.md) provide more diagnostic cases.
For larger inputs you can adjust the bounded search, for example:

```sh
cargo djinn smoke-test --only first_index --max-len 6 --int-bound 12 --timeout 20
```

Larger bounds can cost more solver time. They still do not establish a proof
for inputs outside the explored domain. Even with the default bounds, the
current smoke tester tries both small scalar values and full scalar ranges;
sequence lengths remain bounded.

## 7. Choose reusable constraints with care

As a specification grows, name concepts that recur. A `rel` is a reusable
relation and need not determine a unique output. A `fn` describes a callable
Rust function and normally must determine a unique result. For example,
“is a permutation of” is useful relational vocabulary inside a sorting
function, even though many permutations exist.

A helper should preserve the actual requirement. “Every output element occurs
in the input” does not mean “the output is a permutation.” Even equal lengths
and membership in both directions admit `[1, 1, 2]` becoming `[1, 2, 2]`.
A permutation also preserves the count of each value. The
[language tour](LANGUAGE_TOUR.md) and [sort example](../example/sort/README.md)
show how to express that using counts.

The same review applies to composed functions. Check a callee's preconditions
at every use. Use `#[ensures]` for facts that follow from the body and are useful
to callers; it is a proof obligation, not a way to add a missing constraint to
the body. For a mutating function, consider every observable part of the final
state, including the elements or fields that should remain unchanged. Use
`old(...)` to relate the final state to the entry state.

Do not use `any` just to silence ambiguity. That construct deliberately gives
the implementer a choice and requires `#[weakly_specified]`, including in
calling functions. If the requirement says “first,” choosing a random matching
position changes the requirement. If the requirement truly allows any matching
position, document that choice and review its consequences; see the
[language tour](LANGUAGE_TOUR.md).

## 8. Hand the completed specification to the implementer

Once you have reviewed the contract and its bounded checks, follow the full
verifier and agent setup in [installation](INSTALL.md), then run from your crate:

```sh
cargo djinn implement --limit 5
cargo djinn status
cargo djinn verify
cargo build
```

The first command consumes agent usage, and the limit is an approximate stop
mechanism. An agent run is not guaranteed to finish within it. Review the
reported obligations rather than treating the agent's prose as proof of success.
After implementation, test ordinary Rust callers too: their input validation,
I/O, and other surrounding behavior are outside this specification.

The examples in this workshop illustrate and exercise the specification
frontend and bounded checker. Passing those checks does not claim that the
agent has generated and verified an implementation of `first_index`.

## Practice

Before opening each suggested answer, write down the input cases and the
constraints you would change.

**Return the last occurrence instead.** Keep absence and the result type the
same. Which clause must change, and what should `[5, 5]` return?

<details>
<summary>Suggested answer</summary>

Change `j < i => values[j] != needle;` to `j > i => values[j] != needle;`.
No later index may match. The selected-position and in-bounds clauses stay,
and `[5, 5]` must return `Some(1)`. The uniqueness argument now excludes a
second, larger matching index. Run the bounded checker after changing the clause.

</details>

**Specify a maximum when empty input is possible.** Decide between rejecting
empty lists at the API boundary and representing absence in the output.
Explain why “the result is at least every element” is insufficient.

<details>
<summary>Suggested answer</summary>

For a function returning `i32`, require a nonempty input, require that the
result occurs in it, and require every element to be at most the result.
Alternatively return `Option<i32>`: empty input yields `None`; nonempty input
yields `Some(m)` for an element `m` at least as large as every element.
An upper bound alone allows values larger than the maximum. On an empty input,
the statement “every element is at most the result” places no constraint at all.

</details>

## Review before implementation

Use this short checklist when handing a specification to an agent or another
person:

- **Input domain:** Are empty, boundary, malformed, and duplicate inputs
  handled or intentionally excluded? Can Rust callers establish each precondition?
- **Output:** Does the type represent every required answer? Are absence,
  errors, ties, and all mutated state determined?
- **Meaning:** Can you explain each constraint in terms of the requirement?
  Can an unwanted answer satisfy all of them?
- **Existence and uniqueness:** Can you give a short argument that every valid
  input has exactly one allowed output, or identify the deliberate `any` choices?
- **Defined operations:** Are indexing, unwrapping, arithmetic domains, and
  calls meaningful wherever they appear?
- **Evidence:** Have you distinguished examples, bounded checks, generated
  proofs, and assumptions about the trusted toolchain?

Continue with the [language tour](LANGUAGE_TOUR.md) for the supported forms or
[onboarding](FIRST_STEPS.md) for the complete edit, implement, and verify cycle.
