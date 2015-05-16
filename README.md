# Hygienic macro expansion models

This repository houses Typed Racket implementations of the JFP 2012 "Macros that Work Together" model, and a WIP model for Matthew Flatt's notes on the "set of scopes" model for macro expansion.

This README will act as a development journal as I decipher the prose into a model comparable to the JFP model.

# Goals of this experiment

Hygiene is an old friend of mine. I worked with Mitch Wand and Paul Stansifer on binding-safe metaprogramming, and binding shape specification. The new model for Racket's hygienic macro expander offers more opportunities for exploring the possibilities of expanding the meaning of hygiene. There are two ways to expand hygiene that I'm concerned with:

  1. Provide a generic interface to create new "core forms" that define their own binding structure. This is beneficial for reusing Racket's macro expander to offer macros in a different language (say, a Redex language). This extension should be a simple change to the set of scopes model. Note that the transformer language is still Racket, and not the different target language.
  2. Attach binding intents to macro forms. The "set of scopes" does not immediately accomodate for this. My notes here will be first to decipher Matthew Flatt's notes into a working model (the model at the end of his notes is incomplete and contains small technical errors), and then how to extend that with binding intent.

## Intent: High level

Macros that introduce binding structure (e.g., `match` and `for/fold`) from their input (and elsewhere) do so within the procedural understanding of Dybvig's algorithm. It is mostly natural, but there are meta-level, say, "contracts" that we may wish to express and enforce that can help us debug macro implementations. A contract allows us to state both what definitions a macro will introduce into the current definition context, and which identifiers in the macro input will bind where. If we have a contract system, we can even communicate with compile-time information to state that a contract associated with a syntax object stored previously in a table must be respected in a specific place.

Dybvig's algorithm provides a protection boundary between macro applications and their enclosing scopes. The protection gets resolved in a late-binding what-you-get-is-what-you-meant kind of way. There is no way to state what should happen up front. The marks Dybvig introduces are "usually" what you want, but with "dumpster diving," you can "hygienically" rebind names that [you really shouldn't be able to](http://okmij.org/ftp/Scheme/macros.html#dirty-macros). We want a specification mechanism that is protectable.

### Examples:

#### Definition intent:
```racket
(struct Foo (x y))
```
The canonical example for a well-behaved "non-hygienic" macro in the Racket community is `struct`. We know that this form will introduce phase 0 definitions for

```racket
Foo
Foo?
Foo-x
Foo-y
```
And a phase 1 definition for `Foo`, and these identifiers should all be considered in the same binding context as the original `Foo`.

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

# Experimental notes on "Set of Scopes" binding

These notes are with respect to Matthew Flatt's notes regarding Racket's new experimental macro expander:

  http://www.cs.utah.edu/~mflatt/scope-sets-4/

The model at the end of these notes is missing definitions, and the definition of `prune` has an obvious copy/paste error: the "recursive" call is actually to `strip`, which is an error at least in my understanding.

The missing definitions are `eval`, `fresh`, `fresh-scope`, `mark`, and `biggest-subset`.

First let's discuss the main data structures used in the notes' partial model:

A `DefCtxStore`, what the notes denote with `Σ`, is a burrito for the "fresh monad" and the "state monad". A `Σ` models two global, mutable values for creating unique scopes (a counter, AKA the "fresh monad"), and a table that maps a base symbol plus a set of scopes to a unique name.
I represent this in Typed Racket in the following way:
```racket
(define-type Resolution (HashTable Ctx Name))
(define-type Binds (HashTable Name Resolution))
(struct DefCtxStore ([count : Exact-Nonnegative-Integer]
                     [rib : Binds]))
```
Where a name is modeled by a symbol, as well as scopes and definition context "addresses". The notion of an "address" is an artifact of the JFP model. I've inferred its presence here, since the notes' model does not mention definition contexts.
```racket
(define-type Name Symbol)
(define-type Scope Name)
(define-type Addr Name)
(define-type Ctx (Setof Scope))
```
The nested hash table for names and contexts is a currying of the `(name ctx)` pair.

A piece of syntax attaches a `Ctx` to either an `Atom` or a list of syntax.

## `biggest-subset` finds the lexically closest binder

If an identifier has been bound by a binding form, it is mapped in `Σ` for later resolution.
If it is unbound, the identifier's resolution is simply its symbol.
If it is bound, it can be marked by several extra scopes that did not actually bind the identifier's symbol, so resolution searches for the largest mapped subset of the reference's set of scopes.
If there are multiple "largest" subsets, then we've hit an ambiguous reference. Otherwise, resolution returns the name mapped by the largest context.

```racket
(define (biggest-subset-name who ctx resolutions)
  (define-values (name-biggest dummy num-equal)
    (for/fold ([mnam : Name (hash-ref resolutions ∅ (λ _ who))]
               [msize : Exact-Nonnegative-Integer 0]
               [num : Exact-Nonnegative-Integer 1])
        ([(c n) (in-hash resolutions)]
         #:when (subset? c ctx))
      (define c-size (set-count c))
      (cond
       [(< c-size msize) (values mnam msize num)]
       ;; will lead to an error if c is the largest.
       ;; We thus don't care which name propagates here.
       [(= c-size msize) (values n msize (add1 num))]
       [else (values n c-size 1)])))
  (unless (= num-equal 1)
    (error 'biggest-subset "Ambiguous identifier: ~a" who))
  name-biggest)
```
Notice that the currying in the representation allows this function to easily focus on the identifier's symbolic base.

For better debugging, the `(= c-size msize)` case could construct a list of all the "largest subsets" seen, but I elide good error reporting for simplicity of studying the model.
 
## Both `fresh` and `fresh-scope` use the fresh monad

The number component of Matthew's `Sto` container (my `DefCtxStore` container) is the source of uniqueness for name construction. Every name is suffixed by a count that is always increased after a name is requested.
```racket
(define (fresh-name stx Σ)
  (match stx
    [(Stx (Sym nam) ctx)
     (match-define (DefCtxStore count rib) Σ)
     (values (string->symbol (format "~a~a" nam Σ))
             (DefCtxStore (add1 count) rib))]))
(define fresh-scope fresh-name)
```

## Marking has modes

The notes describe that the marking process has three separate modes: add a scope, remove a scope, and flip a scope. The last mode is the familiar one from Dybvig's algorithm. It is the one I assume is meant when `mark` is written in Matthew's model.

The modes are implemented in a straight-forward manner:
```racket
(define-type Mode (U 'flip 'add 'remove))
(: mode->op : (-> Mode (-> Ctx Scope Ctx)))
(define (mode->op mode)
  (case mode
    [(flip) (λ (ctx scp) (if (set-member? ctx scp)
                             (set-remove ctx scp)
                             (set-add ctx scp)))]
    [(add) (λ (ctx scp) (set-add ctx scp))]
    [(remove) (λ (ctx scp) (set-remove ctx scp))]))
```

For use by the fold over `Stx` that `mark` does in the JFP model, except a context is now just a set of scopes.
```racket
(: mark : (->* (Stx Scope) (Mode) Stx))
(define (mark stx scp [mode 'flip])
  (define op (mode->op mode))
  (let go : Stx ([stx : Stx stx])
   (match stx
     [(Stx (? atom? a) ctx)
      (Stx a (op ctx scp))]
     [(Stx (? list? stxs) ctx)
      (Stx (for/list : (Listof Stx) ([stx (in-list stxs)]) (go stx))
           (op ctx scp))])))
```

## Expression evalution

The notes' model is clearly incomplete, because `eval` must have access to the global table of identifier resolutions and the environment assigning meaning to names. This is where most of my guesswork is.

Unfortunately for strong typing, Typed Racket's `define-refinement` appears to be an the fritz, so I can't statically identify which subset of `Stx` is an identifier. I use a type alias to keep myself a bit more honest.
```racket
(define-type S-Identifier Stx)
```
Now, an environment is much like it was in the JFP model, except now we have `'Letrec-Syntax` instead of `'
```racket
(struct VarTrans ([id : S-Identifier]) #:transparent)
;; Model doesn't have a stop set? Let-Syntax is now Letrec-Syntax..?
(define-type Transform (U 'Fun 'Letrec-Syntax 'Quote VarTrans Val))
(define-type Env (HashTable Name Transform))
```

I then expect the type signature of `eval` to be
```racket
(: seval : (-> Ast Env Ctx DefCtxStore (Values Val Env DefCtxStore)))
```