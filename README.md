# institution

Executable Goguen-style institutions and satisfaction-law testing in Rust.

This workspace contains two publishable crates. The `institution` core trait
models the executable operations of a Goguen-style institution with associated
signature, signature morphism, sentence, model, and error types. Signature
morphisms expose their source and target signatures explicitly; sentence
translation is covariant, model reduct is contravariant, and satisfaction is
executable. Identity and composition make the signature category executable.

The `institution::laws` module observes signature-category, sentence-functor,
model-reduct, and satisfaction laws on supplied examples. For deterministic
operations and well-formed inputs, the results say whether those observations
agree; they do not prove any law universally. Its non-vacuity helper only
reports whether supplied examples produced both truth values.

`institution-conservation` is a downstream adapter that realizes exact
conservation laws and finite traces as an institution. It depends on the
independent conservation foundation; neither foundation depends on the
adapter.

## Architecture boundary

The crate defines the executable institution boundary directly rather than
depending on a generic category framework. It does not provide model
homomorphisms, derive macros, asynchronous operations, or comorphism APIs.
Its law helpers observe examples; implementations and downstream test suites
remain responsible for establishing the laws over their intended domains.
