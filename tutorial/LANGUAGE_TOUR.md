# Language tour

Djinn describes a function through the relationship between its inputs and
outputs. A declaration's body contains logical constraints, and an
implementation supplies an algorithm that satisfies them. Verification
checks that relationship through a translated model of the implementation.

This tour assumes basic Rust knowledge. The complete `djinn!` examples are
independent specification files whose syntax and lowering have been checked.
The tutorial does not supply generated implementations or completed Lean
proofs for these examples. Calling them from Rust requires the crate setup,
implementation, and verification workflow in [First steps](FIRST_STEPS.md).

The [writing specifications workshop](WRITING_SPECS.md) develops a method
for turning requirements into constraints and revising them in response to
counterexamples. This tour explains the language forms used in that process.

- [Inputs, outputs, and constraints](#inputs-outputs-and-constraints)
- [Preconditions, cases, and guarantees](#preconditions-cases-and-guarantees)
- [Integer arithmetic and partial operations](#integer-arithmetic-and-partial-operations)
- [Sequences and universal constraints](#sequences-and-universal-constraints)
- [Existential values and optional results](#existential-values-and-optional-results)
- [Reusable relations](#reusable-relations)
- [Mutation and entry values](#mutation-and-entry-values)
- [Structs, enums, and errors](#structs-enums-and-errors)
- [Recursive specifications](#recursive-specifications)
- [Explicit implementation choices](#explicit-implementation-choices)
- [Supported vocabulary and limitations](#supported-vocabulary-and-limitations)
- [Exercises and further examples](#exercises-and-further-examples)

## Inputs, outputs, and constraints

The minimum of two integers provides a simple example:

```rust
use djinn::djinn;

djinn! {
    pub fn minimum(a: i32, b: i32) -> r: i32 {
        r <= a;
        r <= b;
        r == a || r == b;
    }
}
```

The signature names the return value `r`. All three statements must hold:
the result is at most either input, and it equals one of them. For inputs
`3` and `7`, the only permitted result is `3`.

`r` denotes the return value throughout the body, and `r == a` states an
equality involving that value. The constraints do not assign a value to
`r` or prescribe an execution order. Consequently, assignment with `=`,
`let`, and `return` are not accepted in a constraint body. An implementation
may use an `if`, a standard-library operation, or another algorithm that
produces the required result.

When a signature omits the output name, as in `-> i32`, the default name
is `result`. A `fn` requires an output: a return value, a mutable parameter,
or both.

By default, a `fn` must determine exactly one output for every input admitted
by its preconditions. Removing the last line of `minimum` would admit
many answers: `2` also satisfies `r <= 3` and `r <= 7`. Adding `r > a`
would instead make the body contradictory. These are different failures:
the first violates uniqueness, and the second prevents an output from
existing.

## Preconditions, cases, and guarantees

Clamping illustrates how preconditions and conditional constraints define
an input domain and the result for each case:

```rust
use djinn::djinn;

djinn! {
    #[requires(lo <= hi)]
    #[ensures(lo <= r <= hi)]
    pub fn clamp(x: i32, lo: i32, hi: i32) -> r: i32 {
        lo <= r <= hi;
        x < lo => r == lo;
        x > hi => r == hi;
        lo <= x <= hi => r == x;
    }
}
```

`#[requires(lo <= hi)]` restricts the inputs for which the implementation
must meet its contract. An ordinary Rust caller must establish that
condition before calling `clamp`. The attribute does not insert a runtime
validation check. A Rust driver can satisfy this obligation by validating
user-provided bounds and returning an error when they are reversed. A call
from another Djinn declaration creates a proof obligation for the callee's
precondition.

`#[ensures(...)]` introduces a separate obligation to prove that a property
follows from the body. Once proved, the property is a guarantee available
to callers. Because it must follow from the body, an `ensures` clause
cannot supply a missing constraint needed to determine the result. A
declaration may have several `requires` or `ensures` attributes.

The logical syntax is:

| Form | Meaning |
|---|---|
| `a == b`, `a != b` | Equality and inequality |
| `a < b`, `a <= b`, `a > b`, `a >= b` | Comparisons |
| `lo <= r <= hi` | Both `lo <= r` and `r <= hi` |
| `p && q` | Both constraints hold |
| `p || q` | At least one constraint holds |
| `!p` | The constraint does not hold |
| `p => q;` | If `p` holds, `q` must hold |

An implication says nothing about its right side when its premise is
false. Omitting the last implication in `clamp`, for example, leaves
multiple permitted outputs for inputs strictly inside a range with more
than one value. Parentheses make the grouping explicit when several
logical operators occur in one constraint.

Statement-level `if condition { ... } else { ... }` expresses the same
kind of conditional constraints. Without `else`, the body imposes no
constraint when the condition is false. The named return value cannot
appear in the condition of a statement-level `if`. Implications and
constraints can instead describe alternatives involving an output.

During verification, the main obligations are:

| Obligation | What must be established |
|---|---|
| `unambiguous` | For the same permitted inputs, two outputs satisfying the body are equal |
| `exists` | Every permitted input has an output; for a `fn`, this is derived from implementation correctness |
| `wf` | Indexing, division, unwrapping, and calls are well-defined wherever they matter; emitted when needed |
| `impl_correct` | The translated implementation satisfies the body, terminates, and does not panic on permitted inputs |
| `ens_0`, `ens_1`, … | Each `ensures` property follows from the specification |

These obligations define what verification must establish. Their meaning
is relative to the specification and the toolchain's models; the author
remains responsible for whether the specification expresses the intended
behavior. The scope and assumptions are described under
[verification evidence and limitations](#verification-evidence-and-limitations).

## Integer arithmetic and partial operations

Signatures use Rust's machine integer types, but arithmetic inside
constraints uses mathematical integers. In particular, addition,
subtraction, multiplication, and negation do not wrap at a machine type's
boundary.

```rust
use djinn::djinn;

djinn! {
    pub fn absolute(x: i32) -> r: i64 {
        r >= 0;
        r == x || r == -x;
    }
}
```

The `i64` return type can represent the magnitude of every `i32` input.
For `x == -2147483648`, that magnitude is `2147483648`, which is outside
the `i32` range. A signature returning `i32` would therefore leave this
input without an answer. The implementation must realize the mathematical
result using machine operations that do not overflow, such as widening
before negation.

Integer casts in constraints also preserve the mathematical value.
`x as u8` does not specify truncation or wrapping. If wrapping behavior is
intended, state its arithmetic relationship explicitly. Division and
remainder use mathematical, Euclidean integer semantics, rather than
Rust's truncation toward zero for signed division. For example, in a
constraint `-7 / 3` is `-3` and `-7 % 3` is `2`. For nonnegative operands
and a positive divisor, the usual Rust and specification results agree.

Some operations are defined only for certain arguments; these are called
partial operations. Indexing `values[i]` requires
`0 <= i < values.len()`, and slicing `values[a..b]` requires
`0 <= a <= b <= values.len()`. Division and remainder require a nonzero
divisor, while `option.unwrap()` requires `option.is_some()`.

A logical guard restricts the cases in which a partial expression must be
defined. For example, the following fragment uses a sequence `values` and
an index `i` from its enclosing declaration:

```rust
0 <= i && i < values.len() => values[i] >= 0;
```

The indexed expression must be defined only when the premise holds, and
that premise establishes the required bounds. Logical `&&` and `||` also
use short-circuit guards: the right operand of `&&` is checked assuming
the left holds, and the right operand of `||` is checked assuming the
left does not hold. These rules specify when expressions must be defined
without prescribing branches in the implementation.

## Sequences and universal constraints

Slices, vectors, and arrays are described through their elements. A
maximum can be specified without selecting an iteration algorithm:

```rust
use djinn::djinn;

djinn! {
    #[requires(!values.is_empty())]
    pub fn maximum(values: &[i32]) -> r: i32 {
        r in values;
        for x in values {
            x <= r;
        }
    }

    pub fn count_negative(values: &[i32]) -> r: usize {
        r == values.iter().filter(|x| x < 0).count();
    }
}
```

`r in values` means the sequence contains `r`; `r not in values` means
it does not. `for x in values { ... }` means the constraints hold for
every element. Such a universal constraint is true on an empty sequence,
because there is no element that violates it. The membership constraint
ensures that the result is an actual element, and the precondition ensures
that at least one element exists.

`for i in a..b { ... }` asserts its body for every mathematical integer
index from `a` inclusive to `b` exclusive. If there are no such indices,
it imposes no constraint. It does not construct a Rust iterator or
accumulate state. A constraint body can describe sorted output `out` with
the following fragment:

```rust
for i in 0..out.len() - 1 {
    out[i] <= out[i + 1];
}
```

For an empty sequence, the upper bound is the mathematical integer `-1`,
so the range is empty; there is no unsigned subtraction overflow. The
equivalent vocabulary form is
`out.windows(2).all(|pair| pair[0] <= pair[1]);`.

A returned sequence generally requires constraints on both its length and
its elements. Constraints on a prefix alone leave other elements or an
additional suffix unspecified. The implementation operations `vec![...]`,
`.push()`, and `.collect()` are not accepted as specification syntax.

## Existential values and optional results

`some name: Type { ... }` states that a value exists for which the enclosed
constraints hold. Such a value is called an existential witness, and its
name is in scope until the closing brace. In the following specification,
`m` names a maximum that determines the optional result:

```rust
use djinn::djinn;

djinn! {
    pub fn maximum_or_none(values: &[i32]) -> r: Option<i32> {
        if values.is_empty() {
            r == None;
        } else {
            some m: i32 {
                m in values;
                for x in values {
                    x <= m;
                }
                r == Some(m);
            }
        }
    }
}
```

The lowercase `some` binds an existential witness. Uppercase `Some` is
the Rust `Option` constructor. A single block can introduce several
witnesses, as in `some a: i32, b: i32 { ... }`.

An existential witness need not itself be unique, but a fully specified `fn`'s
outputs still must be. For a search function, the existence of a matching
index does not determine which index to return when matches repeat. A
first-occurrence contract also requires that no earlier index matches.

The optional-value vocabulary includes `None`, `Some(value)`,
`.is_some()`, `.is_none()`, and guarded `.unwrap()`. A sequence's
`.first()` and `.last()` produce optional elements. The current
statement-level `match` supports user-defined enums; it does not handle
`Option` or `Result` patterns.

## Reusable relations

A `rel` names a relation: the combinations of inputs and outputs admitted
by its constraints. It can admit several outputs, or no output for some
inputs, and it has no Rust implementation. A fully specified `fn` using
that relation must still determine unique outputs.

For example, a permutation relation allows many arrangements; sorted
order selects one:

```rust
use djinn::djinn;

djinn! {
    #[total]
    pub rel permutation(values: &[i32]) -> out: Vec<i32> {
        out.len() == values.len();
        for x in values {
            out.iter().filter(|y| y == x).count()
                == values.iter().filter(|y| y == x).count();
        }
        for x in out {
            out.iter().filter(|y| y == x).count()
                == values.iter().filter(|y| y == x).count();
        }
    }

    pub fn sorted(values: &[i32]) -> out: Vec<i32> {
        permutation(values) == out;
        out.windows(2).all(|pair| pair[0] <= pair[1]);
    }
}
```

`permutation(values) == out` says that `values` and `out` satisfy the
relation. It does not execute a permutation-producing helper. Counting
occurrences preserves duplicates: checking membership alone would not
distinguish `[1, 1, 2]` from `[1, 2, 2]`.

`#[total]` adds an existence obligation for a relation: every permitted
input must have at least one output. It does not require uniqueness. A
`fn` already has an existence obligation and cannot carry `#[total]`.
Relations also have any applicable well-formedness and `ensures` obligations.

Relations can use `int`, the unbounded mathematical integer type, in
their signatures. This is useful for lengths, indices, and intermediate
calculations that need no machine representation. `fn` signatures
must use supported Rust types because they describe callable Rust APIs.

Two further forms express whether a relation has an answer:

| Constraint | Meaning and current restriction |
|---|---|
| `x in domain(f)` | `f` has an output for input `x`, including its precondition; `f` must take one parameter |
| `y in range(f)` | Some permitted inputs to `f` produce `y`; `f` must have one output |

Both support `not in`. Neither constructs a collection to iterate over.
The [Sudoku specification](../example/sudoku/src/spec.rs) uses
`g in domain(completion)` to distinguish a puzzle with a completion from
one without one.

## Mutation and entry values

A mutable parameter is an additional output. In the body and in
`ensures`, its bare name means its final value, and `old(name)` means its
value on entry:

```rust
use djinn::djinn;

djinn! {
    pub fn reverse(values: &mut Vec<i32>) {
        values.len() == old(values).len();
        for i in 0..values.len() {
            values[i] == old(values)[values.len() - 1 - i];
        }
    }
}
```

The specification fixes the entire final vector. It does not prescribe
swaps, temporary allocations, or traversal direction. Rust calls it as
`reverse(&mut values)`.

In `requires`, `values` already means the entry value, so `old(values)`
is disallowed there. `old` accepts a mutable parameter's name, not an
arbitrary expression, so the length on entry is written
`old(values).len()`. If a function also returns a value, uniqueness applies
to both the return value and every mutable parameter's final value. All
these outputs require constraints, including elements that should remain
unchanged.

## Structs, enums, and errors

User types are declared as ordinary Rust items next to the `djinn!` block.
A struct with named fields lets an API return several related values:

```rust
use djinn::djinn;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bounds {
    pub lo: i32,
    pub hi: i32,
}

djinn! {
    pub fn bounds(a: i32, b: i32) -> r: Bounds {
        r.lo == a.min(b);
        r.hi == a.max(b);
    }
}
```

Struct literals are not supported inside constraints, so this declaration
specifies the result through its fields. Every field is part of the
returned value; an unconstrained field generally allows multiple outputs
and prevents an unambiguity proof.

User enums support unit, tuple, and named-field variants. A `match`
selects constraints by variant and binds its fields:

```rust
use djinn::djinn;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reading {
    Missing,
    Value(u32),
}

djinn! {
    pub fn value_or_zero(reading: Reading) -> r: u32 {
        match reading {
            Reading::Missing => r == 0,
            Reading::Value(value) => r == value,
        }
    }
}
```

A `match` must cover every variant, either explicitly or with a final `_`
arm. Patterns can ignore tuple fields with `_` or named fields with `..`.
Nested patterns and match guards are not part of the current vocabulary,
and new binders cannot shadow names already in scope.

`Result` makes failure part of the specified output instead of excluding
it with a precondition:

```rust
use djinn::djinn;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DivisionError {
    ZeroDivisor,
}

djinn! {
    pub fn divide(a: u32, b: u32) -> r: Result<u32, DivisionError> {
        if b == 0 {
            r == Err(DivisionError::ZeroDivisor);
        } else {
            some quotient: u32 {
                quotient == a / b;
                r == Ok(quotient);
            }
        }
    }
}
```

The zero-divisor case has the specified error as its answer. In the other
case, the quotient of two `u32` values fits in `u32`, so every pair of
inputs has a representable result. `Ok` and `Err` construct results;
Rust's `?` operator and `Result::unwrap` are not available inside
constraints. Ordinary Rust callers can use `match` or `?` when consuming
the generated function's result.

## Recursive specifications

Recursion is useful when a value has a natural inductive definition. For
example, the sum of the first `n` elements is the sum of the first `n - 1`
elements plus the last element:

```rust
use djinn::djinn;

djinn! {
    #[requires(0 <= n <= values.len())]
    #[decreases(n)]
    pub rel prefix_sum(values: &[i32], n: int) -> sum: int {
        if n == 0 {
            sum == 0;
        } else {
            sum == prefix_sum(values, n - 1) + values[n - 1];
        }
    }
}
```

`#[decreases(n)]` supplies a measure for the recursive definition's
termination proof. Each recursive call must decrease it within a
well-founded domain. The precondition supplies nonnegativity here, and
the nonzero branch ensures `n - 1` is a valid smaller index. The annotation
states the proposed measure; the generated proof must still establish
that it decreases at each recursive call.

Both `fn` and `rel` can be directly recursive and require a `decreases`
annotation when they call themselves. Several measures are compared
lexicographically: `#[decreases(a, b)]` first compares `a`, then `b` when
`a` is unchanged. The generated proof automation may not establish a
termination argument that requires additional mathematical results.

This relation defines a mathematical sum. A `fn` using it may have an
iterative implementation, because recursion in the specification does not
prescribe recursion in Rust. The termination of the specification
definition and the termination of an implementation are separate proof
requirements; the latter is part of `impl_correct`.

## Explicit implementation choices

When the contract deliberately permits several outputs, `any` identifies
a choice left to the implementation:

```rust
use djinn::djinn;

djinn! {
    #[weakly_specified]
    #[requires(x in values)]
    #[ensures(index < values.len() && values[index] == x)]
    pub fn find_any(values: &[i32], x: i32) -> index: usize {
        any candidate: usize where
            candidate < values.len() && values[candidate] == x;
        index == candidate;
    }
}
```

For `[4, 9, 4]` and target `4`, either index `0` or index `2` is permitted.
The contract specifies neither a preferred index nor a probability
distribution over the choices. A later reimplementation or optimization
may select a different permitted index.

`any candidate: T where condition;` brings `candidate` into scope for the
rest of its block. Each choice is modeled as a function of the inputs
and surrounding `for` variables, so a choice inside an indexed `for` may
differ by position. The choice declaration does not prescribe an
assignment or search algorithm. The existential binder `some` has a
different role: it introduces a witness while retaining the function's
output uniqueness requirement.

Functions with choices have the following obligations and restrictions:

- A function containing `any` must carry `#[weakly_specified]`. Every
  `fn` that calls a weakly specified function must carry it too, even
  when the caller's own result discards some of the choice.
- Unambiguity is proved for fixed inputs and fixed choices. Other
  output ambiguity is still rejected. Existence and implementation
  correctness are still required.
- Every `ensures` must hold for every admissible choice, not just the one
  selected by the current implementation. The `where` clause is the
  guarantee about the chosen value.
- `any` is for functions; a relation already admits ambiguity and uses
  `some`. A `#[weakly_specified]` attribute without any own or inherited
  choice is rejected.
- Weakly specified mutual recursion is unsupported.

A stable first-occurrence contract therefore requires a fully specified
`fn`: the result is a matching index, and every earlier position differs
from the target. A contract using `any` is appropriate only if all its
permitted outputs are acceptable, so those permitted choices require
review as part of the contract. The [choice
example](../example/choice/src/spec.rs) demonstrates choices in error
messages, loops, and callers.

## Supported vocabulary and limitations

Djinn accepts the following selected vocabulary. Its resemblance to Rust
syntax does not imply support for arbitrary Rust expressions.

| Area | Available forms |
|---|---|
| Scalar types | Signed and unsigned Rust integers, `bool`, `char`; mathematical `int` in relation signatures |
| Sequence types | Slices, `Vec<T>`, arrays, `&str`, `String` |
| Sequence constraints | `len`, `is_empty`, `contains`, `in`, `not in`, indexing, half-open slicing, `first`, `last` |
| Iterator-like vocabulary | `.iter().all(...)`, `.iter().any(...)`, `.iter().filter(...).count()`, `.iter().sum()`, `.windows(2).all(...)` |
| Numeric vocabulary | `abs`, `min`, `max`, `pow` with a nonnegative exponent |
| Structured values | Named-field structs, user enums, `Option<T>`, `Result<T, E>` |
| Maps | `HashMap<K, V>` with `len`, `is_empty`, `contains_key`, and `get` |
| Alternatives | `cases { ... }` requires at least one of its enclosed statements to hold; group a multi-constraint alternative in a supported block such as `some` |

Strings are viewed as UTF-8 byte sequences. `len()` counts bytes, and
indexing and slicing use byte positions. They do not describe Unicode
characters or grapheme clusters. `"text"` and `b"text"` provide byte
literals, and `.as_bytes()` exposes that same view. See
[strmap](../example/strmap/src/spec.rs) for strings and maps. The map model
uses entries with unique keys, and `.get(&key)` returns an optional value
in the specification.

Ordinary Rust functions declared in a specification file can also be
called from constraints when their signatures fit the supported subset.
These are called ambient functions. Their meaning is their translated
Rust behavior, which becomes a dependency of the specification. The `bump`
helper in [strmap](../example/strmap/src/spec.rs) is an example; sequences
and maps are not supported in ambient function signatures.

Current limitations include floating-point types, tuples in signatures,
generic user structs and enums, nested references, and borrowed return
values. Collections such as `HashSet` and `BTreeMap` have no supported
model. Ownership wrappers such as `Box` and `Arc` are not specification
value types. Arbitrary methods, closures, I/O, `async`, `unsafe`, and
side-effecting Rust statements are outside the constraint language.

Parsing, printing, network access, and other application behavior can be
written in ordinary Rust outside the block. Such code is not automatically
verified. Implementations of Djinn functions also depend on the operations
modeled by Charon, Aeneas, and the trusted model library.

### Verification evidence and limitations

Parser and lowering acceptance show that the frontend accepts the syntax and
can emit Lean expressions for it. A bounded smoke test searches for
counterexamples within its supported input domain. Neither establishes the
contract for all inputs.
A successful `cargo djinn verify` checks proofs for the current
specification and translated implementation, subject to the toolchain's
[assumptions and limitations](README.md#assumptions-and-limitations).

The smoke tester currently reports struct and `Result` outputs as
unsupported, and recursive relations can exceed its unfolding
limit. These reports do not mean the corresponding language features are
rejected, and they are not successful checks of those specifications.
The language also does not specify timing, allocation cost, or
side-channel behavior.

## Exercises and further examples

The following exercises apply the distinctions between output constraints,
input domains, and permitted choices. Each contract can be checked with
`cargo djinn smoke-test` before implementation:

1. Change `minimum` to a maximum. Keep the disjunction so the result is
   one of the inputs.
2. Specify the first occurrence of a target under the precondition that
   it occurs. Test your reasoning on repeated values and a match at index
   zero.
3. Make that search return `Option<usize>` for arbitrary inputs. Specify
   both the absent case and the first-occurrence rule.
4. Specify an in-place replacement at one valid index. State that the
   vector's length and every other element remain unchanged.

The [writing workshop](WRITING_SPECS.md) develops the search exercises
and explains how to diagnose incomplete specifications.

The repository provides further examples with increasing scope:

| Example | What to study |
|---|---|
| [clamp](../example/clamp/src/spec.rs) | Scalar constraints, preconditions, and a Rust driver |
| [sort](../example/sort/src/spec.rs) | Permutation relations, multiplicities, and mutation |
| [broken](../example/broken/README.md) | Examples designed to expose specification mistakes |
| [strmap](../example/strmap/src/spec.rs) | Bytes, map lookup, and an ambient Rust helper |
| [choice](../example/choice/src/spec.rs) | Explicit implementation choices and inherited choices |
| [sudoku](../example/sudoku/src/spec.rs) | Existence, optional results, and a unique choice among solutions |
| [lz77](../example/lz77/src/spec.rs) | Recursive relations, enums, and an optimization objective |

The [onboarding guide](FIRST_STEPS.md) supplies the workflow for implementing
and verifying these contracts. For syntax details beyond the tour, the current
[parser](../rust-djinn/syntax/src/parse.rs) and
[lowering code](../rust-djinn/syntax/src/lower.rs) define the accepted
forms and their translation.
