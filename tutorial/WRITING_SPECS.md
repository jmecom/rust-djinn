# Writing Djinn specifications

Writing a Djinn program requires a precise description of its observable
behavior. That description determines the permitted inputs, the meaning of the
result, and the treatment of exceptional cases. An implementation agent supplies
an algorithm and proofs that it satisfies the description. The author remains
responsible for determining whether the description expresses the requirements.

This chapter develops a specification for finding the first occurrence of a
value in a list. An initial draft admits several answers for some inputs;
refining its constraints resolves that ambiguity. The
[language tour](LANGUAGE_TOUR.md) explains individual syntax forms, and
[First steps](FIRST_STEPS.md) provides the crate setup and implementation commands.

Reading the chapter requires no tool installation. Checking the drafts requires
the Djinn CLI and Z3 from the [setup reference](INSTALL.md). To run the examples,
use the new-crate configuration in First steps, replace `src/spec.rs` with each
complete block below, and run the commands from that crate's directory.
Replace `pub use spec::abs;` in `src/lib.rs` with
`pub use spec::first_index;`, keeping the existing `spec` and `solution` module
declarations. The drafts are alternatives, not functions to paste into the same
file together.

## 1. Input domain and result type

The requirement is:

> Given a list of integers and a value to find, return the index of its first
> occurrence. Return no index if the value is absent.

Several input-output examples make its boundary cases explicit:

| Input list | Value | Required result | Decision this records |
|---|---:|---|---|
| `[]` | `5` | `None` | Empty input is valid |
| `[5]` | `5` | `Some(0)` | Indices start at zero |
| `[3, 5, 5]` | `5` | `Some(1)` | Duplicates select the first occurrence |
| `[3, 5, 5]` | `4` | `None` | Absence is a normal result |
| `[-2, 7]` | `7` | `Some(1)` | A match at the final index is included |

These examples record decisions that the specification must express for all
inputs. The list is borrowed and unchanged, which suggests `&[i32]` as its type.
A Rust index is represented by `usize`. Since a matching index need not exist,
the result is `Option<usize>`. Every input is valid under this requirement, so
the function needs no `#[requires]` clause.

An alternative API could require that the value occurs and return `usize`.
That contract would require callers to establish membership before making the
call. The choice between these APIs depends on whether callers need an absence
result or already guarantee that a match exists.

## 2. An incomplete specification

The following draft captures presence and absence but leaves part of the
requirement unspecified:

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

If the value occurs, the draft requires an index `i` within the list whose
element matches. The result must be `Some(i)`.
If the value is absent, the result is `None`. `some` introduces an existential
witness: it asserts that such an `i` exists. It does not instruct the
implementation to search for one in any particular way.

The `for` statement asserts a property at every input index `j`.
The implication `j == i => values[j] == needle` constrains the selected index.
Other indices impose no condition yet. Iterating over `0..values.len()` also
keeps every indexed access in bounds, including when the list is empty.

For `[3, 5, 5]` and `needle = 5`, both `Some(1)` and `Some(2)` satisfy this draft.
It specifies a matching occurrence,
without saying which occurrence to return.

## 3. Refinement from a counterexample

The bounded checker can identify this ambiguity:

```sh
cargo djinn smoke-test --only first_index
```

The draft produces an `AMBIGUOUS` unambiguity result. The exact counterexample
can vary, but it has repeated matching values and two allowed result indices.
The requirement permits only the earlier match. A permitted result must
therefore exclude every earlier matching position.

The second implication inside the loop expresses this additional constraint:

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

Running the same smoke test on this version gives consistency, existence,
unambiguity, and well-formedness checks with no counterexample within their
bounds. This is evidence about the bounded search, rather than a proof for
arbitrary inputs.

The branch condition depends on the input. This follows a language restriction:
Djinn rejects statement conditions that depend on the named output, such as
`if out.is_some()`. Input cases organize this specification, and the statements
within each case constrain the result.

## 4. Existence and uniqueness

An informal argument provides a further check of the specification. Existence
means that every permitted input admits an output. Uniqueness means that any
two outputs satisfying the constraints for that input are equal.

**Existence:** If `needle` is absent, `None` satisfies the second branch.
Otherwise the finite list has a first matching position. Its index is in bounds,
its element matches, and every earlier element differs. Returning that index
therefore satisfies the first branch.

**Uniqueness:** In the absent case, only `None` is allowed. In the present case,
suppose two different indices were allowed. The smaller one would be a match
before the larger one, contradicting the larger index's “no earlier match”
constraint. The indices, and therefore the results, must be equal.

This argument has not been checked by the proof toolchain. Its role here is to
explain why the constraints determine the required result and to support review
of later changes. It leaves the implementation free to choose loops, early
returns, vectorization, or a search order consistent with that result.

## 5. Constraint dependencies

The contribution of a constraint can be examined by removing it and constructing
an unwanted answer that the remaining constraints admit. For this function:

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
anything. A universal constraint states what holds for the indices in its
range; it does not itself establish that a candidate index belongs to that range.

Clauses need not be logically independent. A redundant assertion can make intent
easier to review, provided its role is understood. Identifying which guarantees
follow from other clauses helps distinguish intentional redundancy from a
missing requirement.

## 6. Diagnostic interpretation

Smoke testing looks for several different problems. A proof attempt can also
fail because the tools or agent cannot solve the obligation, so a failed proof
attempt alone does not establish that a specification is wrong.

| Finding | Interpretation | Typical response |
|---|---|---|
| Ambiguity | The constraints admit multiple results for an input | Identify the intended answer and add the missing requirement |
| Missing output | A permitted input has no representable answer satisfying the body | Handle the case, widen the result type, or justify a precondition |
| Contradiction | The reported requirements cannot hold together | Compare the conflicting requirements with the intended behavior |
| Ill-formed expression | An operation is used outside its domain | Establish index bounds, nonzero divisors, or callee preconditions |
| Failed `ensures` | A claimed consequence does not follow from the body | Repair the body or correct the claim |
| Unsupported, skipped, or timed out | The check did not establish a result | Inspect the reported limitation before drawing a conclusion |

For example, `r >= 0; r == x || r == -x;` describes the absolute
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

## 7. Reusable relations and composition

Recurring concepts can be expressed as named relations. A `rel` is a reusable
relation and need not determine a unique output. A `fn` describes a callable
Rust function and normally must determine a unique result. For example,
“is a permutation of” is useful relational vocabulary inside a sorting
function, even though many permutations exist.

A permutation preserves the count of each value. Element membership alone is
insufficient: even equal lengths and membership in both directions admit
`[1, 1, 2]` becoming `[1, 2, 2]`. The
[language tour](LANGUAGE_TOUR.md) and [sort example](../example/sort/README.md)
show how to express that using counts.

Composition introduces further obligations. Every call must satisfy the
callee's preconditions. A `#[ensures]` clause exposes a fact that follows from
the body; proving it does not add a missing constraint to the body. A mutating
function must also determine each observable part of its final state, including
elements or fields that remain unchanged. The `old(...)` form refers to the
entry state when expressing these relationships.

The `any` construct deliberately permits an implementation choice and requires
`#[weakly_specified]`, including in calling functions. Its use changes the
contract: permitting any matching position would no longer express the
requirement to return the first one. When several outputs are acceptable, the
permitted choice needs an explicit description and review. The
[language tour](LANGUAGE_TOUR.md) explains these semantics.

## 8. Implementation and verification

After review of the contract and its bounded checks, implementation can proceed
with the full verifier and agent setup in [installation](INSTALL.md). The
following commands run from the crate directory:

```sh
cargo djinn implement --limit 5
cargo djinn status
cargo djinn verify
cargo build
```

The first command consumes agent usage, and its limit is an approximate stop
mechanism. The run may finish without completing the proofs. Acceptance depends
on the verifier's results for the reported obligations. Ordinary Rust callers
also require application-level checks because their input validation, I/O, and
surrounding behavior are outside this specification.

The examples in this workshop illustrate and exercise the specification
frontend and bounded checker. Passing those checks does not claim that the
agent has generated and verified an implementation of `first_index`.

## Exercises

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

## Specification review

Review can be organized around six aspects of the contract:

- **Input domain:** Empty, boundary, malformed, and duplicate inputs are handled
  or intentionally excluded, and Rust callers can establish each precondition.
- **Output:** The type represents every required answer, including absence,
  errors, ties, and the final values of mutated state.
- **Meaning:** Each constraint corresponds to a requirement, and known unwanted
  answers are excluded by the complete body.
- **Existence and uniqueness:** An ordinary `fn` admits exactly one output for
  every permitted input. Choices introduced by `any` are explicit. A `rel` may
  admit several outputs or none; any required existence guarantee is identified.
- **Defined operations:** Indexing, unwrapping, arithmetic operations, and calls
  are used within their domains.
- **Evidence:** Examples, bounded checks, generated proofs, and assumptions about
  the trusted toolchain are identified separately.

Continue with the [language tour](LANGUAGE_TOUR.md) for the supported forms or
[onboarding](FIRST_STEPS.md) for the complete edit, implement, and verify cycle.
