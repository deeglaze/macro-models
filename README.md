# Hygienic macro expansion models

This repository houses Typed Racket implementations of the JFP 2012 "Macros that Work Together" model, and a WIP model for Matthew Flatt's notes on the "set of scopes" model for macro expansion.

This README will act as a development journal as I decipher the prose into a model comparable to the JFP model.

# Experimental notes on "Set of Scopes" binding

These notes are with respect to Matthew Flatt's notes regarding Racket's new experimental macro expander:

  http://www.cs.utah.edu/~mflatt/scope-sets-4/

Hygiene is an old friend of mine. I worked with Mitch Wand and Paul Stansifer on binding-safe metaprogramming, and binding shape specification. The new model for Racket's hygienic macro expander offers more opportunities for exploring the possibilities of expanding the meaning of hygiene. There are two ways to expand hygiene that I'm concerned with:

  1. Provide a generic interface to create new "core forms" that define their own binding structure. This is beneficial for reusing Racket's macro expander to offer macros in a different language (say, a Redex language). This extension should be a simple change to the set of scopes model. Note that the transformer language is still Racket, and not the different target language.
  2. Attach binding intents to macro forms. The "set of scopes" does not immediately accomodate for this. My notes here will be first to decipher Matthew Flatt's notes into a working model (the model at the end of his notes is incomplete and contains small technical errors), and then how to extend that with binding intent.

## Intent: High level

Macros that introduce binding structure (e.g., ```racket match``` and ```racket for/fold```) from their input (and elsewhere) do so within the procedural understanding of Dybvig's algorithm. It is mostly natural, but there are meta-level, say, "contracts" that we may wish to express and enforce that can help us debug macro implementations. A contract allows us to state both what definitions a macro will introduce into the current definition context, and which identifiers in the macro input will bind where. If we have a contract system, we can even communicate with compile-time information to state that a contract associated with a syntax object stored previously in a table must be respected in a specific place.

Dybvig's algorithm provides a protection boundary between macro applications and their enclosing scopes. The protection gets resolved in a late-binding what-you-get-is-what-you-meant kind of way. There is no way to state what should happen up front. The marks Dybvig introduces are "usually" what you want, but with "dumpster diving," you can "hygienically" rebind names that [you really shouldn't be able to][oleg]. We want a specification mechanism that is protectable.

### Examples:

#### Definition intent:
```racket
(struct Foo (x y))
```
The canonical example for a well-behaved "non-hygienic" macro in the Racket community is ```racket struct```. We know that this form will introduce phase 0 definitions for

```racket
Foo
Foo?
Foo-x
Foo-y
```
And a phase 1 definition for ```racket Foo```, and these identifiers should all be considered in the same binding context as the original ```racket Foo```.

We should be able to simply state this and check either
   (a) all these and only these identifiers are introduced definitions by the macro application, or
   (b) at least these identifiers are introduced definitions by the macro application.

#### Binding input intent:

The language I developed with Paul and Mitch is an algebraic data type that states specifically which identifiers will be bound where. In a sense, it's a restricted language for guiding a marking process.
In the set of scopes model, a lambda binding form does a few things:

  1. generate a fresh name for the binder (as close to the original name as possible, for debugging purposes),
  2. generate a fresh scope for the lambda form itself,
  3. update the name resolution table to map the input binder marked with the scope to the fresh name,
  4. update the environment to back-translate the fresh name back to the marked identifier,
  5. mark the body with the import scope to show that it is "in the context" of that scope,
  6. continue expansion with the base context extended with the new scope.

Lambda binding `(λ x e)` is the simplest of all binding forms: `x` binds in `e`. It has one name that binds in one place. The language Paul and I developed under Mitch's advisement describes much more. Consider the `let*` form in Racket:

```racket
(let* ([x0 e0]
       [x1 e1]
       ...
       [xn en])
  body)
```
Every one of `xi` is bound in `body`, and `xi` is bound in `e[i+1]` (for `i` in `0 ... n-1`).
If we treat the clauses of the `let*` as their own piece of data, then all of the `xi` are "exported" for later binding, but there is still an expressed scoping relationship. The binding happens in `let*`.
We write this with ML-like data structures in the following way (pseudocode),
```racket
(define-ADT Let*Clauses
  (Let*Nil)
  (Let*Clause Binder Expr Let*Clauses #:bind [0 2] #:export (2 #:shadow 0)))
```
This states that if we have clauses of the form `([x0 e0] . rest)`, then `x0` is bound in `rest` (0th element bound in 2nd element of `Let*Clause`), and all exported identifiers in `rest`, as well as `x0` are available to be imported for binding later, where `x0` is shadowed by any `x0` exported by `rest`.

This ADT-like language can be interpreted in the set-of-scopes model as a scope generation and marking discipline. Each `#:bind` creates a new scope that both marks the identifiers being imported, and the location in which the identifiers are imported. Everything identified as an `Expr` is another piece of syntax to expand: the origin contexts in which they are expanded are the starting context extended by the import scopes generated by the ADT marking procedure.

This is all well and good for treating `let*` as a core form, but how do we ensure that the original binding structure as described here is implemented by the expanded form? Can we make a "scope intent" that will raise an error if it lands in a core form that doesn't treat the scope in the intended way?

If we accidentally implement `let` instead of `let*`, the macro expander should error on expanding
```racket
(let ([x 0])
 (let* ([x x]
        [y x])
   x))
```
because the `x` in the `[y x]` clause is not scoped by the `[x x]` clause. It is instead scoped by the outside let-bound `x`.

The scope marks we might see upon expanding `let` are
```racket
(let ([x^{a} 0])
  (let*^{a} ([x^{a} x^{a}]
             [y^{a} x^{a}])
    x^{a}))
```
and then after some "intent scoping" in the `let*`, we might see
```racket
(let ([x^{a} 0])
  (let*^{a} ([x^{a,ib} x^{a}]
             [y^{a,ib,ic} x^{a,ib}])
    x^{a,ib,ic}))
```
The "i" here is to state that these scope objects are intended to be in some isomorphic scope structure. Let's say we try to expand `let*` as `let`:
```racket
(let ([x^{a} 0])
  (let ([x^{a,ib} x^{a}]
        [y^{a,ib,ic} x^{a,ib}])
    x^{a,ib,ic,b}))
```
and now we match "intent" with "result". An indentifier in a core form's binding position must have its intent scope objects mapped to introduced scope objects. Here there is only one introduced scope, `b`, so there is no isomorphism between `{ib,ic}` and `{b}`. Error.

Let's say we expand to the natural expansion:
```racket
(let ([x^{a} 0])
  (let ([x^{a,ib} x^{a}])
    (let*^{a,b} ([y^{a,ib,ic} x^{a,ib}])
       x^{a,ib,ic})))
```
The `let` form will introduce a scope `b`, which is permuted with `ib`, so there is no error.
Expansion continues post-permutation to give
```racket
(let ([x^{a} 0])
  (let ([x^{a,b} x^{a}])
    (let ([y^{a,b,ic} x^{a,b}])
       x^{a,b,ic})))
```
where the `let` form introduces a new scope `c`, which is permuted with `ic`, so there is no error.
The final expansion resolves all the names
```racket
(let ([x 0])
  (let ([x1 x])
    (let ([y x1])
      x1)))
```

We will see if intent permutations are really all we need. I foresee problems arising when we delegate binding responsibilities to other macros - who is at fault for failing to produce the expected binding structure? Can we catch intent mismatch when two intents are given to the same identifier?

[oleg]: Oleg Kiselyov http://okmij.org/ftp/Scheme/macros.html#dirty-macros