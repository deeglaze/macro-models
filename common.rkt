#lang typed/racket/base
(require (for-syntax typed/racket/base)
         racket/match)
(provide (all-defined-out))
(define-type Name Symbol)
(struct Sym ([sym : Name]) #:transparent)

;; All the primitives
(struct -stx-e ()) (define stx-e (-stx-e))
(struct -mk-stx ()) (define mk-stx (-mk-stx))
(struct -CONS ()) (define CONS (-CONS))
(struct -CAR ()) (define CAR (-CAR))
(struct -CDR ()) (define CDR (-CDR))
(struct -LIST ()) (define LIST (-LIST))
(struct -PLUS ()) (define PLUS (-PLUS))
(define-type Prim (U -stx-e -mk-stx -CONS -CAR -CDR -LIST -PLUS))
(define-predicate prim? Prim)

;; All the compile-time primitives
(struct -new-defs ()) (define new-defs (-new-defs))
(struct -def-bind ()) (define def-bind (-def-bind))
(struct -lvalue ()) (define lvalue (-lvalue))
(struct -lexpand ()) (define lexpand (-lexpand))
(define-type TPrim (U -new-defs -def-bind -lvalue -lexpand))
(define-predicate tprim? TPrim)

(define-type Atom (U Sym Number Boolean String Prim TPrim))
(define-predicate atom? Atom)

(begin-for-syntax
 (: format-id : (All (a ...) (-> Identifier String a ... Identifier)))
 (define (format-id id fmt . args)
   (define args*
     (for/list : (Listof Any) ([arg (in-list args)])
               (if (identifier? arg)
                   (syntax-e arg)
                   arg)))
   (datum->syntax id (string->symbol (apply format fmt args*)))))

(define-syntax (mk-Types stx)
  (syntax-case stx ()
    [(_  [Stx stxs? S-Identifier s-identifier? s-identifiers? Ctx]
         [Var App Ast ast? Fun Val val?]
         δ)
     (with-syntax
         ([Stx-a/los (format-id #'Stx "~a-a/los" #'Stx)]
          [Stx? (format-id #'Stx "~a?" #'Stx)])
       #'
       (begin
         (struct Var ([name : Name]) #:transparent)
         (struct App ([ast0 : Ast]
                      [asts : (Listof Ast)])
                 #:transparent) ;; head form, and payload.
         (define-type Ast (U Var App Val))
         (define-predicate ast? Ast)
         
         ;; Value AST
         (struct Fun ([var : Var]
                      [ast : Ast]) #:transparent)

         (struct Stx ([a/los : (U Atom (Listof Stx))]
                      [ctx : Ctx]) #:transparent)

         (: stxs? : (-> Any Boolean : (Listof Stx)))
         (define (stxs? x) (and (list? x) (andmap Stx? x)))

         (: s-identifier? : (-> Any Boolean : #:+ (S-Identifier @ 0)))
         (define (s-identifier? s)
           (and (Stx? s)
                (Sym? (Stx-a/los s))))
         (define-type S-Identifier Stx) ;; Unchecked!! Should use Refinement, but that shit's broken.

         (: s-identifiers? : (-> Any Boolean : #:+ ((Listof S-Identifier) @ 0)))
         (define (s-identifiers? x)
           (and (stxs? x)
                (andmap s-identifier? x)))

         ;; XXX: unfortunately the typing situation makes it hard (impossible?)
         ;; to just use Racket functions as primitives. We would need
         ;; bounded polymorphism on polydots. i.e.
         ;; (All (a ... <: Val) (-> a ... Val))
         (: prim-table : (HashTable Prim (-> (Listof Val) Val)))
         (define prim-table
           ((inst make-hash Prim (-> (Listof Val) Val))
            (list
             (cons
              stx-e
              (match-lambda
               [(list (Stx (? val? val) _)) val]
               [_ (error 'undefined-stx-e)]))
             (cons
              mk-stx
              (match-lambda
               [(list (? atom? a) (Stx (? val?) ctx))
                (Stx a ctx)]
               [(list stxs (Stx (? val?) ctx))
                (Stx (cast stxs (Listof Stx)) ctx)]
               [vs (error 'undefined-mk-stx "~a" vs)]))
             (cons
              CONS
              (λ ([vs : (Listof Val)])
                 (match vs
                   [(list v0 (? list? vs)) (cons v0 vs)]
                   [_ (error 'cons-bad-input "~a" vs)])))
             (cons
              CAR
              (λ ([vs : (Listof Val)])
                 (match vs
                   [(list (cons v0 vs)) v0]
                   [_ (error 'car-bad-input "~a" vs)])))
             (cons
              CDR
              (λ ([vs : (Listof Val)])
                 (match vs
                   [(list (cons v0 vs)) vs]
                   [_ (error 'cdr-bad-input "~a" vs)])))
             (cons LIST (λ ([vs : (Listof Val)]) vs)))))

         (: δ : (-> Prim (Listof Val) Val))
         (define (δ prim vs)
           ((hash-ref prim-table prim (λ _ (error 'unknown-primitive "~a" prim))) vs))))]))
