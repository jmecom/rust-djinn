# Writing Djinn specifications

This tutorial explains how to express a program's intended behavior in Djinn.
It covers the language, the process of refining a specification, and the tools
used to check and implement it. The emphasis is on the author's decisions:
which inputs are valid, which outputs are permitted, and whether the constraints
cover the required behavior.

Djinn specifications are written inside `djinn!` blocks in ordinary Rust crates.
A specification relates inputs to outputs. An implementation agent supplies
Rust code and Lean proofs, and the verifier checks that the translated code
satisfies the relation. The surrounding Rust program calls the resulting
function through its ordinary Rust signature.

## Audience and prerequisites

The tutorial assumes familiarity with Rust functions, borrowing, collections,
and `Option`. It introduces the logical concepts used in specifications as they
arise; knowledge of Lean is not required. The explanations and exercises can be
read without installing the tools.

Running a supplied implementation requires Rust and Cargo. Checking a draft for
bounded counterexamples additionally requires the Djinn CLI and Z3. Generating
and verifying a new implementation requires Charon, Aeneas, and Lean; automated
implementation also requires a configured coding agent. The
[setup reference](INSTALL.md) describes these stages separately.

## Reading sequence

The chapters contain the setup, examples, and explanations needed for the
tutorial. Links to the repository's examples and source files provide further
material.

| Chapter | Scope |
|---|---|
| [First steps](FIRST_STEPS.md) | Read an existing specification, diagnose an ambiguous absolute-value function, and create a crate |
| [Writing specifications](WRITING_SPECS.md) | Derive a first-occurrence search specification from requirements and examine its existence and uniqueness properties |
| [Language tour](LANGUAGE_TOUR.md) | Study the supported syntax and semantics, including relations, mutation, structured values, and explicit choices |
| [Setup reference](INSTALL.md) | Build the tools and configure the optional verifier, agent, and editor components |

Readers interested primarily in specification design can begin with the
writing chapter and consult the language tour as needed. First steps provides
the crate configuration and command-line workflow for running the examples.

## An introductory specification

The maximum of a nonempty list must occur in the list and be at least as large
as every element. These two requirements give the following specification:

```rust
use djinn::djinn;

djinn! {
    #[requires(list.len() >= 1)]
    pub fn maximum(list: &[i32]) -> r: i32 {
        r in list;
        for x in list { x <= r; }
    }
}
```

The signature names the result `r`. The first constraint requires membership;
the second states that every element is at most `r`. Both must hold. Membership
alone would allow a smaller element, while the second constraint alone would
allow a value larger than the maximum. Their conjunction determines one result
for each nonempty input list.

The `requires` attribute is a precondition: callers must establish that the list
is nonempty. Without it, the empty input would admit no result because no value
occurs in an empty list. This example illustrates the two questions that guide
specification review: whether an answer exists for each permitted input, and
whether that answer is unique.

The block is a specification-file example. Calling `maximum` from Rust also
requires the crate wiring, implementation, and verification described in
[First steps](FIRST_STEPS.md).

## Assumptions and limitations

A successful proof establishes a property of the written specification and the
translated implementation. It does not establish that the specification
expresses the intended requirement. Reviewing the input domain, output cases,
and constraints therefore remains part of the author's work.

The verification result depends on Djinn's translation and axiom audit, Charon,
Aeneas, Lean, and the library models used by the implementation. This repository
is research software, and the presence of a model does not imply that it has
been independently audited. Ordinary Rust callers must establish preconditions;
the macro does not insert runtime checks for them or verify the surrounding
application.

The tutorial distinguishes examples, bounded searches, and proofs. An example
illustrates a particular input and result. A smoke test searches within finite
bounds and the subset supported by its solver translation. A successful
`cargo djinn verify` checks the implementation's proof obligations through the
configured toolchain. Parser acceptance or a smoke test with no counterexample
is not equivalent to that verification result.

The complete tutorial examples have been checked by the parser and lowering
code. The worked scalar and search drafts have also been exercised with the
bounded checker. These checks do not constitute newly generated and verified
implementations of every example. Runtime performance, allocation cost, and
absence of timing side channels are outside the specified guarantees.

## Further examples

The repository includes larger specifications and implementations. Each
example's README describes its recorded verification state and commands.
`cargo djinn status` reads the saved state of a Djinn crate; a fresh verification
requires the full toolchain.

| Example | Relevant concepts |
|---|---|
| [clamp](../example/clamp/README.md) | Scalar constraints, preconditions, counting, and ordinary Rust callers |
| [sort](../example/sort/README.md) | Ordering, permutation constraints, and benchmark workloads |
| [broken](../example/broken/README.md) | Deliberately flawed specifications and smoke-test diagnostics |
| [strmap](../example/strmap/README.md) | Strings, structs, map operations, and modeled Rust functions |
| [sudoku](../example/sudoku/README.md) | A larger relational specification |
| [lz77](../example/lz77/README.md) | Recursive compression and decompression specifications |
| [choice](../example/choice/README.md) | Explicit implementation choices with `any` and `#[weakly_specified]` |
| [gzip](../example/gzip/README.md) | Compression specifications with implementation choices and performance workloads |

The [historical calibration example](../example/calib/README.md) contains
plain-Rust sort and maximum functions with manually emitted Lean obligations.
It uses its own verification commands rather than the current Djinn workflow.
