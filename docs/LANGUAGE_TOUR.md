# Language tour

Djinn describes the relationship between a function's inputs and outputs.
The implementation supplies an algorithm; verification checks that the
algorithm has the specified behavior. The syntax resembles Rust, but the
body of a Djinn declaration contains logical constraints rather than
instructions to execute.

This tour assumes basic Rust knowledge. For installation and the edit,
implement, verify workflow, start with [First steps](FIRST_STEPS.md). Each
complete `djinn!` example below is a specification-file example: it still
needs the crate setup, generated implementation, and verification described
there before it can be called from Rust. Examples are independent unless
stated otherwise.

For a worked method of turning a requirement into constraints, including
counterexamples and revisions, use the [Writing specifications
workshop](WRITING_SPECS.md) alongside this tour.

- [Inputs, outputs, and constraints](#inputs-outputs-and-constraints)
- [Preconditions, cases, and guarantees](#preconditions-cases-and-guarantees)
- [Numbers and operations that need guards](#numbers-and-operations-that-need-guards)
- [Sequences and universal constraints](#sequences-and-universal-constraints)
- [Existential values and optional results](#existential-values-and-optional-results)
- [Reusable relations](#reusable-relations)
- [Mutation and entry values](#mutation-and-entry-values)
- [Structs, enums, and errors](#structs-enums-and-errors)
- [Recursive specifications](#recursive-specifications)
- [Leaving an explicit choice](#leaving-an-explicit-choice)
- [The supported Rust-like vocabulary](#the-supported-rust-like-vocabulary)
- [Practice and larger examples](#practice-and-larger-examples)

## Inputs, outputs, and constraints

Start with the smaller of two integers:

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

`r` is available throughout the body; it is not a variable that starts
uninitialized and is later assigned. `r == a` states equality. `r = a`,
`let`, and `return` do not belong in a constraint body. There is no runtime
loop or branch order to choose here. The generated Rust implementation
could use an `if`, a standard-library operation, or another algorithm.

If you omit the output name, as in `-> i32`, its name is `result`. Naming
it explicitly usually makes a specification easier to read. A `fn` needs
an output: a return value, a mutable parameter, or both.

A normal `fn` must determine exactly one output for every input admitted
by its preconditions. Removing the last line of `minimum` would admit
many answers: `2` also satisfies `r <= 3` and `r <= 7`. Adding `r > a`
would instead make the body contradictory. These are different failures:
the first violates uniqueness, and the second prevents an output from
existing.

## Preconditions, cases, and guarantees

Clamping makes the input assumptions and cases explicit:

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
validation check. For user-provided bounds, validate them in the Rust
driver and report an error before making the call. A call from another
Djinn declaration creates a proof obligation for the callee's precondition.

`#[ensures(...)]` asks for a separate proof that the property follows from
the body. It documents a guarantee that callers can rely on. It does not
repair an incomplete body: adding an `ensures` clause cannot replace a
missing constraint needed to determine the result. Several `requires` or
`ensures` attributes may appear on one declaration.

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
false. Omitting the last implication in `clamp`, for example, leaves the
in-range case ambiguous. Use parentheses when combining logical operators
so the intended grouping is visible.

Statement-level `if condition { ... } else { ... }` expresses the same
kind of conditional constraints. Without `else`, the body imposes no
constraint when the condition is false. The named return value cannot
appear in the condition of a statement-level `if`; use implications or
explicit constraints when describing alternatives for an output.

During verification, the main obligations are:

| Obligation | What must be established |
|---|---|
| `unambiguous` | For the same permitted inputs, two outputs satisfying the body are equal |
| `exists` | Every permitted input has an output; for a `fn`, this is derived from implementation correctness |
| `wf` | Indexing, division, unwrapping, and calls are well-defined wherever they matter; emitted when needed |
| `impl_correct` | The Rust implementation satisfies the body, terminates, and does not panic on permitted inputs |
| `ens_0`, `ens_1`, … | Each `ensures` property follows from the specification |

These claims are relative to the specification and the verification
toolchain's models. They do not establish that the specification expresses
your intent, or verify the ordinary Rust code surrounding it.

## Numbers and operations that need guards

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

The wider return type matters. For `x == -2147483648`, the mathematical
answer is `2147483648`, which fits in `i64` but not `i32`. Changing this
signature to return `i32` would leave that input without an answer. The
implementation must use operations that realize the mathematical result
without overflowing; writing a constraint does not make Rust arithmetic
unbounded.

Integer casts in constraints also preserve the mathematical value.
`x as u8` does not specify truncation or wrapping. If wrapping behavior is
intended, state its arithmetic relationship explicitly. Division and
remainder use mathematical, Euclidean integer semantics, rather than
Rust's truncation toward zero for signed division. For example, in a
constraint `-7 / 3` is `-3` and `-7 % 3` is `2`. For nonnegative operands
and a positive divisor, the usual Rust and specification results agree.

Partial operations need a domain condition. For `values[i]`, establish
`0 <= i < values.len()`; for `values[a..b]`, establish
`0 <= a <= b <= values.len()`; division and remainder require a nonzero
divisor; `option.unwrap()` requires `option.is_some()`.

Logical guards express those conditions locally. For example, inside a
declaration with a sequence `values` and index `i`, this constraint is
well-defined even when `i` is out of bounds:

```rust
0 <= i && i < values.len() => values[i] >= 0;
```

The index matters only when the premise holds. `&&` and `||` also carry
the appropriate short-circuit guards into their right operands. This is
about which expressions must be defined, not an instruction to generate
a particular branch in Rust.

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
every element. An empty sequence makes such a universal constraint true,
so the membership constraint and precondition are essential in `maximum`.

`for i in a..b { ... }` quantifies over mathematical integer indices from
`a` inclusive to `b` exclusive. If there are no such indices, it imposes
no constraint. It does not construct a Rust iterator or accumulate state.
For example, a constraint body can describe sorted output `out` as:

```rust
for i in 0..out.len() - 1 {
    out[i] <= out[i + 1];
}
```

For an empty sequence, the upper bound is the mathematical integer `-1`,
so the range is empty; there is no unsigned subtraction overflow. The
equivalent vocabulary form is
`out.windows(2).all(|pair| pair[0] <= pair[1]);`.

Specify both the length and the elements when constructing a sequence.
Constraining just a prefix usually leaves the rest of a returned vector
unspecified. `vec![...]`, `.push()`, and `.collect()` are implementation
operations, not specification syntax.

## Existential values and optional results

`some name: Type { ... }` means that a value exists for which the enclosed
constraints hold. Its scope ends at the closing brace. Here it gives a
name to a maximum before wrapping it in `Some`:

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

The lowercase `some` is an existential binder. Uppercase `Some` is the
Rust `Option` constructor. You can introduce several witnesses together,
as in `some a: i32, b: i32 { ... }`.

An existential witness need not itself be unique, but a normal `fn`'s
outputs still must be. Writing “there exists an index containing the
target” does not specify which index a search function returns. Add a
rule such as “no earlier index contains it” if you want the first match.

For optional values, use `None`, `Some(value)`, `.is_some()`, `.is_none()`,
and guarded `.unwrap()`. A sequence's `.first()` and `.last()` produce
optional elements. The current statement-level `match` supports
user-defined enums; it does not handle `Option` or `Result` patterns.

## Reusable relations

A `rel` defines specification vocabulary. It can admit several outputs,
or no output for some inputs, and it has no Rust implementation. A `fn`
using that relation must resolve any ambiguity in its own outputs.

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

`#[total]` requests an existence proof for a relation: every permitted
input has at least one output. It does not request uniqueness. A `fn`
already owes existence and cannot carry `#[total]`. Relations still owe
any applicable well-formedness and `ensures` proofs.

Relations can use `int`, the unbounded mathematical integer type, in
their signatures. This is useful for lengths, indices, and intermediate
calculations without promising a machine representation. `fn` signatures
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
arbitrary expression; write `old(values).len()`, not `old(values.len())`.
If a function also returns a value, uniqueness applies to both the return
value and every mutable parameter's final value. Remember to constrain
all of them, including elements that should remain unchanged.

## Structs, enums, and errors

Declare user types as ordinary Rust items next to the `djinn!` block.
Named-field structs let an API return several related values:

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

Constrain the fields rather than writing a struct literal inside the
specification. Every field is part of the returned value, so leaving one
unconstrained usually prevents an unambiguity proof.

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

Match all variants or provide a final `_` arm. Patterns can ignore tuple
fields with `_` or named fields with `..`; nested patterns and match
guards are not part of the current vocabulary. New binders cannot shadow
names already in scope.

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

Here every pair of inputs has an answer, including zero divisors. The
error variant is fixed by the specification. `Ok` and `Err` construct
results; Rust's `?` operator and `Result::unwrap` are not available inside
constraints. Ordinary Rust callers can use their usual `match` or `?`
when consuming the generated function's result.

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
the nonzero branch ensures `n - 1` is a valid smaller index. A measure
does not override these requirements: a declaration that simply repeats
the same input cannot be justified by adding the attribute.

Both `fn` and `rel` can be directly recursive and require a `decreases`
annotation when they call themselves. Several measures are compared
lexicographically: `#[decreases(a, b)]` first compares `a`, then `b` when
`a` is unchanged. More elaborate termination arguments may exceed the
generated proof automation. Start with direct recursion and a simple
nonnegative measure.

This defines a mathematical sum and does not choose a recursive Rust
algorithm. If a `fn` uses it, that function may have an iterative
implementation. Also distinguish the termination of this specification
definition from the separate `impl_correct` proof that an implementation
terminates.

## Leaving an explicit choice

Sometimes several outputs are acceptable and choosing among them is
deliberately part of implementation design. `any` exposes that choice:

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
This does not specify the first occurrence, a random occurrence, or a
different occurrence on each call. It leaves an admissible choice to the
implementation, and a later reimplementation or optimization may change
that choice.

`any candidate: T where condition;` brings `candidate` into scope for the
rest of its block. Each choice is modeled as a function of the inputs
and surrounding `for` variables, so a choice inside an indexed `for` may
differ by position. It is not an imperative assignment or a search
algorithm. By contrast, `some` only introduces an existential witness
and does not relax a normal function's output uniqueness requirement.

The restrictions and guarantees matter:

- A function containing `any` must carry `#[weakly_specified]`. Every
  `fn` that calls a weakly specified function must carry it too, even
  when the caller's own result discards some of the choice.
- Unambiguity is proved for fixed inputs **and fixed choices**. Other
  output ambiguity is still rejected. Existence and implementation
  correctness are still required.
- Every `ensures` must hold for every admissible choice, not just the one
  selected by the current implementation. The `where` clause is the
  guarantee about the chosen value.
- `any` is for functions; a relation already admits ambiguity and uses
  `some`. A `#[weakly_specified]` attribute without any own or inherited
  choice is rejected.
- Weakly specified mutual recursion is unsupported. Keep choice-bearing
  APIs simple and review the choices made by their implementations.

Prefer a normal `fn` when the choice is observable behavior you want to
keep stable. For the first occurrence, replace `any` with a constrained
index and a universal statement that all earlier positions differ from
the target. Use `any` only when every output it permits is acceptable.
The [choice example](../example/choice/src/spec.rs) demonstrates choices
in error messages, loops, and callers.

## The supported Rust-like vocabulary

Djinn accepts a selected vocabulary, not arbitrary Rust expressions.
These forms are useful when reading existing examples:

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
called from constraints when their signatures fit the supported ambient
function subset. Their meaning is their translated Rust behavior, so
they become part of what your specification relies on. This is different
from a `rel` defined entirely by constraints. The `bump` helper in
[strmap](../example/strmap/src/spec.rs) is a small example; sequences and
maps are not supported in ambient function signatures.

Current limitations include floating-point types, tuples in signatures,
generic user structs and enums, nested references, and borrowed return
values. Collections such as `HashSet` and `BTreeMap` have no supported
model. Ownership wrappers such as `Box` and `Arc` are not specification
value types. Arbitrary methods, closures, I/O, `async`, `unsafe`, and
side-effecting Rust statements are outside the constraint language.

Keep parsing, printing, network access, and other application code in
ordinary Rust outside the block. Such code is not automatically verified.
Implementations also depend on the operations modeled by Charon, Aeneas,
and the trusted model library; a Rust feature's existence does not imply
that this verification pipeline supports it.

The project is research software. Parser acceptance, a clean bounded
smoke test, and a completed proof are different milestones. Smoke tests
can find counterexamples but do not establish a contract for all inputs;
unsupported constructs or a search bound may limit them. A successful
`cargo djinn verify` is the relevant proof result for the current
specification and implementation, subject to the toolchain's trust
assumptions described in the [README](../README.md#verification-and-its-limits).
The language does not specify timing, allocation cost, or side-channel
behavior.

In particular, the smoke tester currently reports struct and `Result`
outputs as unsupported, and recursive relations can exceed its unfolding
limit. These reports do not mean the corresponding language features are
rejected, and they are not successful checks of those specifications.

## Practice and larger examples

Try one change at a time and run `cargo djinn smoke-test` before asking
an agent to implement it:

1. Change `minimum` to a maximum. Keep the membership-style disjunction
   so the result is one of the inputs.
2. Specify the first occurrence of a target under the precondition that
   it occurs. Test your reasoning on repeated values and a match at index
   zero.
3. Make that search return `Option<usize>` for arbitrary inputs. Specify
   both the absent case and the first-occurrence rule.
4. Specify an in-place replacement at one valid index. State that the
   vector's length and every other element remain unchanged.

The [writing workshop](WRITING_SPECS.md) develops the search exercises
and explains how to diagnose incomplete specifications.

Then read the examples in increasing scope:

| Example | What to study |
|---|---|
| [clamp](../example/clamp/src/spec.rs) | Scalar constraints, preconditions, and a Rust driver |
| [sort](../example/sort/src/spec.rs) | Permutation relations, multiplicities, and mutation |
| [broken](../example/broken/README.md) | Examples designed to expose specification mistakes |
| [strmap](../example/strmap/src/spec.rs) | Bytes, map lookup, and an ambient Rust helper |
| [choice](../example/choice/src/spec.rs) | Explicit implementation choices and inherited choices |
| [sudoku](../example/sudoku/src/spec.rs) | Existence, optional results, and a unique choice among solutions |
| [lz77](../example/lz77/src/spec.rs) | Recursive relations, enums, and an optimization objective |

Return to [First steps](FIRST_STEPS.md) to implement and verify your own
function. For syntax details beyond the tour, the current
[parser](../rust-djinn/syntax/src/parse.rs) and
[lowering code](../rust-djinn/syntax/src/lower.rs) define the accepted
forms and their translation.
