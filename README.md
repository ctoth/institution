# institution

Executable Goguen-style institutions and satisfaction-law testing in Rust.

This workspace contains one publishable crate, `institution`. Its core trait
models the executable operations of a Goguen-style institution with associated
signature, signature morphism, sentence, model, and error types. Signature
morphisms expose their source and target signatures explicitly; sentence
translation is covariant, model reduct is contravariant, and satisfaction is
executable.

The `institution::laws` module observes both sides of one supplied satisfaction
square. For deterministic operations and well-formed inputs, its result says
whether those two observations agree; it does not prove the satisfaction
condition universally. Its non-vacuity helper only reports whether the supplied
well-formed, deterministic examples produced both truth values. It cannot
establish global non-vacuity.

## Architecture boundary

The crate defines the executable institution boundary directly. It does not
provide a generic category framework, derive or helper macros, asynchronous
operations, or comorphism APIs. In particular, the trait does not encode or
claim to verify signature-category identity or composition laws, sentence-
translation functoriality, model-reduct functoriality, or universal satisfaction
invariance. Implementations and downstream test suites remain responsible for
those laws.
