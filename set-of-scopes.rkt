#lang typed/racket
(require "common.rkt")

(define-type Scope Name)
(define-type Ctx (Setof Scope))

(: ∅ : (Setof Scope))
(define ∅ (seteq))

(mk-Types [Stx stxs? S-Identifier s-identifier? s-identifiers? Ctx]
          [Var App Ast ast? Fun Val val?]
          δ)
(define-type Val1 (U Fun Atom Stx))
(define-type Val (U Val1 (Listof Val)))
(define-predicate val? Val)

(struct VarTrans ([id : S-Identifier]) #:transparent)
;; Model doesn't have a stop set? Let-Syntax is now Letrec-Syntax..?
(define-type Transform (U 'Fun 'Letrec-Syntax 'Quote VarTrans Val))
(define-type Env (HashTable Name Transform))

;; mflatt's notation
;;    m^{a,b} -> m8 
;; translates to (hash 'm (hash (seteq 'a 'b) 'm8))
;; so other scope sets are possible for 'm.
(define-type Resolution (HashTable Ctx Name))
(define-type Binds (HashTable Name Resolution))
(struct DefCtxStore ([count : Exact-Nonnegative-Integer]
                     [rib : Binds]))

(: seval : (-> Ast Val))
(define (seval ast) (error 'eval-undefined))

;; Σ₂ = Σ₁+{id-new ↦ name-new}
;; but id-new ≡ Stx('nam, ctx)
;; so Σ₂ = Σ₁[nam ↦ Σ₁(nam)[ctx ↦ name-new]]
(: store : (-> DefCtxStore Stx Name DefCtxStore))
(define (store Σ id nam)
  (match-define (DefCtxStore count rib) Σ)
  (match-define (Stx (Sym id-nam) ctx) id)
  (define upd (hash-set (hash-ref rib id-nam (λ _ ((inst hash Ctx Name))))
                        ctx nam))
  (DefCtxStore count (hash-set rib id-nam upd)))

;; Give scope meaning to primitives
(: sexpand : (-> Stx Env Ctx DefCtxStore (Values Stx DefCtxStore)))
(define (sexpand stx ξ ctx-e Σ)
  (match-define (Stx a/los ctx) stx)

  (: application : (-> Stx (Listof Stx) (Values Stx DefCtxStore)))
  (define (application rtor rnd)
    (define-values (appform Σ₁)
      (sexpand* '() (cons rtor rnd) ξ ctx-e Σ))
    (values (Stx appform ctx) Σ₁))
  
  (match a/los
    ;; lambda
    [(list (? s-identifier? id-lam) (? s-identifier? id-arg) stx-body)
     #:when (eq? 'Fun (hash-ref ξ (resolve id-lam Σ)))
     ;; For hygienic binding, we create a new name for the binder
     (define-values (nam-new Σ₁) (fresh-name id-arg Σ))
     (define-values (scp-new Σ₂) (fresh-scope id-arg Σ₁))
     ;; And rename it.
     (define id-new (mark id-arg scp-new))
     (define Σ₃ (store Σ₂ id-new nam-new))
     ;; And make references understand the name transform.
     (define ξ-new (hash-set ξ nam-new (VarTrans id-new)))
     ;; Then we continue expanding in the extended context.
     (define-values (stx-expbody Σ₄)
       (sexpand (mark stx-body scp-new) ξ-new (set-add ctx-e scp-new) Σ₃))
     (values (Stx (list id-lam id-new stx-expbody) ctx) Σ₁)]

    ;; quote
    [(list (? s-identifier? id-quote) _)
     #:when (eq? 'Quote (hash-ref ξ (resolve id-quote Σ)))
     (values stx Σ)]

    ;; syntax
    [(list (? s-identifier? id-syntax) syn)
     #:when (eq? 'Syntax (hash-ref ξ (resolve id-syntax Σ)))
     (values (Stx (list id-syntax (prune syn ctx-e)) ctx) Σ)]

    ;; macro binding
    [(list (? s-identifier? id-ls) (? s-identifier? id-mac) rhs body)
     #:when (eq? 'Letrec-Syntax (hash-ref ξ (resolve id-ls Σ)))
     ;; Let-Syntax is another binding form, so we create a fresh name for the binder
     (define-values (nam-new Σ₁) (fresh-name id-mac Σ))
     (define-values (scp-new Σ₂) (fresh-scope id-mac Σ₁))
     (define id-new (mark id-mac scp-new))
     (define Σ₃ (store Σ₂ id-new nam-new))
     (define ξ-new (hash-set ξ nam-new (seval (parse (mark rhs scp-new) Σ₃))))
     (define stx-newbody (mark body scp-new))
     (define ctx-newe (set-add ctx-e scp-new))
     (sexpand stx-newbody ξ-new ctx-newe Σ₃)]

    ;; (macro) application
    [(cons head args)
     (cond
      [(s-identifier? head)
       (define trans (hash-ref ξ (resolve head Σ)))
       (cond
        ;; macro application
        [(val? trans)
         ;; SIC: the notes skip 1 and use 2.
         (define-values (scp-orig Σ₂) (fresh-scope (Stx (Sym 'a) ∅) Σ))
         (define-values (scp-new Σ₃) (fresh-scope (Stx (Sym 'a) ∅) Σ₂))
         (define exp
           (seval (App trans (list (mark (mark stx scp-orig) scp-new)))))
         (unless (Stx? exp) (error 'seval "Macro transformation produced non-syntax: ~a" exp))
         ;; Note: dropping ξ₁ environment
         (sexpand (mark exp scp-new) ξ (set-add ctx-e scp-orig) Σ₃)]
        [(eq? trans 'Stop)
         (values stx Σ)]
        [else (application head args)])]
      [else (application head args)])]

    ;; (Stx Sym _) is an identifier.
    [(? Sym?)
     (match (hash-ref ξ (resolve stx Σ))
       [(VarTrans id-new) (values id-new Σ)]
       [bad (error 'sexpand "Bad reference: ~a" bad)])]

    [bad (error 'sexpand "Bad syntax: ~a" bad)]))

(: sexpand* : (-> (Listof Stx) (Listof Stx) Env Ctx DefCtxStore (Values (Listof Stx) DefCtxStore)))
(define (sexpand* done stxs ξ ctx-e Σ)
  (match stxs
    ['() (values (reverse done) Σ)]
    [(cons stx0 stxs*)
     ;; XXX: is this right?
     (define-values (done0 Σ₁) (sexpand stx0 ξ ctx-e Σ))
     (sexpand* (cons done0 done) stxs* ξ ctx-e Σ₁)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: mark : (-> Stx Scope Stx))
(define (mark stx scp)
  (match stx
    [(Stx (? atom? a) ctx)
     (Stx a (set-add ctx scp))]
    [(Stx (? list? stxs) ctx)
     (Stx (for/list : (Listof Stx) ([stx (in-list stxs)]) (mark stx scp))
          (set-add ctx scp))]))

(: mark* : (-> Stx Ctx Stx))
(define (mark* stx ctx*)
  (match stx
    [(Stx (? atom? a) ctx)
     (Stx a (set-union ctx ctx*))]
    [(Stx (? list? stxs) ctx)
     (Stx (for/list : (Listof Stx) ([stx (in-list stxs)]) (mark* stx ctx*))
          (set-union ctx ctx*))]))

(: strip : (-> Stx Val))
(define (strip stx)
  (match stx
    [(Stx (? atom? a) ctx) a]
    [(Stx (? list? stxs) _) (map strip stxs)]))

;; ----------------------------------------
;; Simple parsing of already-expanded code
;;  (used for expand-time expressions, instead of
;;   modeling multiple phases):
(: parse : (-> Stx DefCtxStore Ast))
(define (parse stx Σ)
  (match stx
    [(Stx (list (? s-identifier? id-λ) (? s-identifier? id-arg) body) ctx)
     #:when (eq? 'lambda (resolve id-λ Σ))
     ;; Understand the identifiers in the current context.
     (Fun (Var (resolve id-arg Σ)) (parse body Σ))]
    [(Stx (list (? s-identifier? id-quote) stx) ctx)
     #:when (eq? 'quote (resolve id-quote Σ))
     (strip stx)]
    [(Stx (list (? s-identifier? id-syntax) stx) ctx)
     #:when (eq? 'syntax (resolve id-syntax Σ))
     stx]
    [(Stx (cons ast0 asts) ctx)
     (App (parse ast0 Σ) (for/list ([rand (in-list asts)]) (parse rand Σ)))]
    [(? s-identifier? id) (Var (resolve id Σ))]
    [_ (error 'parse "Bad syntax ~a" stx)]))

(: subst : (-> Ast Var Ast Ast))
(define (subst from var to)
  (match from
    [(Var n)
     (if (equal? from var)
         to
         from)]
    [(App ast0 asts)
     (App (subst ast0 var to)
          (for/list ([ast (in-list asts)]) (subst ast var to)))]
    [(? val? val) (subst-val val var to)]))

(: subst-val : (-> Val Var Ast Val))
(define (subst-val from var to)
  (match from
    [(Fun (== var) ast) from]
    [(Fun (and var2 (Var nam2)) ast)
     (define var3 (Var (variable-not-in to nam2)))
     (Fun var3 (subst (subst ast var2 var3) var to))]
    [(? atom? a) a]
    [(? list? vals)
     (for/list : (Listof Val) ([val (in-list vals)]) (subst-val val var to))]
    [(? Stx? stx) stx]))

(: variable-not-in : (-> Ast Name Name))
(define (variable-not-in ast nam)
  (define names (support ast))
  ;; nam prefix followed by a natural number
  (define nam-match (regexp (format "^~a([1-9][0-9]*)|0$" nam)))
  (if (set-member? names nam)
      ;; Find all numerically suffixed `nam` symbols,
      ;; produce the next highest number.
      (string->symbol
       (format
        "~a~a"
        nam
        (add1
         (for*/fold ([max-num : Exact-Nonnegative-Integer 0])
             ([n (in-set names)]
              [ns (in-value (symbol->string n))])           
           (match (and (regexp-match-exact? nam-match ns)
                       (regexp-match nam-match ns))
             [#f max-num]
             [(list num-str _)
              (max max-num (assert (string->number num-str) exact-nonnegative-integer?))])))))
      nam))

(: support : (-> Ast (Setof Name)))
(define (support ast)
  (match ast
    [(Var n) (seteq n)]
    [(App a0 as) (support* (support a0) as)]
    [(? list? asts) (support* (seteq) asts)]
    [(Fun (Var n) ast) (set-add (support ast) n)]
    [(Stx a/los ctx) (set-union ctx (support a/los))]
    ;; Atom and Vdefs
    [_ (seteq)]))

(: support* : (-> (Setof Name) (Listof Ast) (Setof Name)))
(define (support* base lst)
  (for/fold ([S : (Setof Name) base])
      ([a (in-list lst)])
    (set-union S (support a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: resolve : (-> Stx DefCtxStore Name))
(define (resolve stx Σ)
  (match stx
    [(Stx (Sym nam) ctx)
     (match-define (DefCtxStore count rib) Σ)
     (cond
      [(hash-ref rib nam #f) => (λ (ctx/names)
                                   (biggest-subset-name nam ctx ctx/names))]
      ;; unbound
      [else nam])]
    [_ (error 'resolve "Expected identifier")]))

(: biggest-subset-name : (-> Name Ctx Resolution Name))
(define (biggest-subset-name who ctx resolutions)
  (define-values (max-ctx name-biggest dummy num-equal)
    (for/fold ([mctx : Ctx ∅]
               [mnam : Name (hash-ref resolutions ∅ (λ _ who))]
               [msize : Exact-Nonnegative-Integer 0]
               [num : Exact-Nonnegative-Integer 1])
        ([(c n) (in-hash resolutions)])
      (define c-size (set-count c))
      (cond
       [(< c-size msize) (values mctx mnam msize num)]
       ;; will lead to an error if mctx is the largest.
       ;; We thus don't care which name propagates here.
       [(= c-size msize) (values mctx n msize (add1 num))]
       [else (values c n c-size 1)])))
  (unless (= num-equal 1)
    (error 'biggest-subset "Ambiguous identifier: ~a" who))
  name-biggest)

(: prune : (-> Stx Ctx Stx))
(define (prune stx ctx-e)
  (match stx
    [(Stx (? atom? a) ctx) (Stx a (set-subtract ctx ctx-e))]
    [(Stx (? list? stxs) ctx)
     (Stx (for/list : (Listof Stx) ([stx (in-list stxs)]) (prune stx ctx-e))
          (set-subtract ctx ctx-e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: fresh-name : (-> Stx DefCtxStore (Values Name DefCtxStore)))
(define (fresh-name stx Σ)
  (match stx
    [(Stx (Sym nam) ctx)
     (match-define (DefCtxStore count rib) Σ)
     (values (string->symbol (format "~a~a" nam Σ))
             (DefCtxStore (add1 count) rib))]))
(define fresh-scope fresh-name)
