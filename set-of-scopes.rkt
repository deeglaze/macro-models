#lang typed/racket
(require "common.rkt")

(define-type Scope Name)
(define-type Addr Name)
(define-type Ctx (Setof Scope))

(: ∅ : (Setof Scope))
(define ∅ (seteq))

(mk-Types [Stx stxs? S-Identifier s-identifier? s-identifiers? Ctx]
          [Var App Ast ast? Fun Val val?]
          δ)
(define-type Sigma (U Addr #f))
(struct Vdefs ([σ : Sigma]))
(define-type Val1 (U Fun Atom Stx Vdefs))
(define-type Val (U Val1 (Listof Val)))
(define-predicate val? Val)

(struct VarTrans ([id : S-Identifier]) #:transparent)
;; Model doesn't have a stop set? Let-Syntax is now Letrec-Syntax..?
(define-type Transform (U 'Fun 'Letrec-Syntax 'Quote 'Stop VarTrans Val))
(define-type Env (HashTable Name Transform))

;; mflatt's notation
;;    m^{a,b} -> m8
;; translates to (hash 'm (hash (seteq 'a 'b) 'm8))
;; so other scope sets are possible for 'm.
(define-type Resolution (HashTable Ctx Name))
(define-type Binds (HashTable Name Resolution))
(struct DefCtxStore ([count : Exact-Nonnegative-Integer]
                     [rib : Binds]))

(: seval : (-> Ast Env Ctx DefCtxStore (Values Val Env DefCtxStore)))
(define (seval ast ξ ctx-e Σ)
  (match ast
    [(App head args)
     (match head
       [(Fun var body)
        (match args
          [(list arg)
           (define-values (val ξ₁ Σ₁) (seval arg ξ ctx-e Σ))
           (seval (subst body var val) ξ₁ ctx-e Σ₁)]
          [_ (error 'undefined-fn-args)])]
       [(? prim? prim)
        (define-values (vals ξ₁ Σ₁) (seval* '() args ξ ctx-e Σ))
        (values (δ prim vals) ξ₁ Σ₁)]

       ;; Model in paper has this after ast_op, but catch-all...?
       [(== lvalue eq?)
        (match args
          [(list arg)
           (define-values (stx-pre ξ₁ Σ₁) (seval arg ξ ctx-e Σ))
           (define stx (assert stx-pre Stx?))
           (define trans (hash-ref ξ (resolve stx Σ₁)
                                   (λ _ (error 'local-value "Unbound id: ~a" stx))))
           (unless (val? trans)
             (error 'seval "Local value not a value: ~a" trans))
           (values trans ξ₁ Σ₁)]
          [_ (error 'undefined-lvalue-args)])]

       ;; TODO SoS
       [(== lexpand eq?)
        (match args
          [(list ast-expr ast-stops ast-defs)
           (define-values (stx-expr-pre ξ₁ Σ₁) (seval ast-expr ξ ctx-e Σ))
           (define stx-expr (assert stx-expr-pre Stx?))
           (define-values (stops-pre ξ₂ Σ₂) (seval ast-stops ξ₁ ctx-e Σ₁))
           (define stops (assert stops-pre s-identifiers?))
           (define-values (vd-pre ξ₃ Σ₃) (seval ast-defs ξ₂ ctx-e Σ₂))
           (match-define (Vdefs σ) vd-pre)

           (: ξ-stops : Env)
           (define ξ-stops
             (for/fold ([ξ-stops : Env (no-stops ξ₃)])
                 ([id-stop : S-Identifier (in-list stops)])
               (hash-set ξ-stops (resolve id-stop Σ₃) 'Stop)))

           ;; unmark current mark(s)...?
           (define flip (if σ (λ ([s : Stx]) (mark s σ)) (λ ([s : Stx]) s)))
           (define stx-new (flip stx-expr))
           (define-values (stx Σ₄) (sexpand stx-new ξ-stops ctx-e Σ₃))
           (values (flip stx) ξ₃ Σ₄)])]

       [(== new-defs eq?)
        (match args
          ['()
           ;; Pun σ as the basis for the generated name
           (define-values (σ Σ₁) (fresh-name (Stx (Sym 'σ) ∅) Σ))
           (values (Vdefs σ) ξ Σ₁)]
          [_ (error 'undefined-new-defs-args)])]

       ;; TODO SoS
       [(== def-bind eq?)
        (match args
          [(list ast-defs ast-id)
           (match-define-values ((Vdefs σ) ξ₁ Σ₁) (seval ast-defs ξ ctx-e Σ))
           (define-values (id-val ξ₂ Σ₂) (seval ast-id ξ₁ ctx-e Σ₁))
           (define id (assert id-val s-identifier?))
           ;; Defining id freshens it.
           (define-values (nam-new Σ₃) (fresh-name id Σ₂))
           (define-values (scp-new Σ₄) (fresh-scope id Σ₃))
           (define id-new (mark id scp-new))
           (define Σ₅ (store Σ₄ id-new nam-new))
           (values 0 (hash-set ξ nam-new (VarTrans id-new)) Σ₅)]

          ;; bind expand-time value in definition context
          [(list ast-defs ast-id ast-stx)
           (match-define-values ((Vdefs σ) ξ₁ Σ₁)
                                (seval ast-defs ξ ctx-e Σ))
           (define-values (id-val ξ₂ Σ₂) (seval ast-id ξ₁ ctx-e Σ₁))
           (define-values (stx-val ξ₃ Σ₃) (seval ast-stx ξ₂ ctx-e Σ₁))
           (define flip (if σ (λ ([s : Stx]) (mark s σ)) (λ ([s : Stx]) s)))
           (define-values (val ξ₄ Σ₄)
             (seval (parse (flip (assert stx-val Stx?)) Σ₃)
                    ξ₃
                    ctx-e
                    Σ₃))

           (define id (assert id-val s-identifier?))
           (define-values (nam-new Σ₅) (fresh-name id Σ₄))
           (define-values (scp-new Σ₆) (fresh-scope id Σ₅))
           (define id-new (mark id scp-new))
           (define Σ₇ (store Σ₆ id-new nam-new))
           (values 0 (hash-set ξ₄ nam-new val) Σ₇)])]

       [_ ;; head just an ast
        (define-values (head-e ξ₁ Σ₁) (seval head ξ ctx-e Σ))
        (seval (App head-e args) ξ₁ ctx-e Σ₁)])]
    [(? val? val) (values val ξ Σ)]))

(: seval* : (-> (Listof Val) (Listof Ast) Env Ctx DefCtxStore
                (Values (Listof Val) Env DefCtxStore)))
(define (seval* vals asts ξ ctx-e Σ)
  (match asts
    ['() (values (reverse vals) ξ Σ)]
    [(cons ast0 asts*)
     (define-values (val0 ξ₁ Σ₁) (seval ast0 ξ ctx-e Σ))
     (seval* (cons val0 vals) asts* ξ₁ ctx-e Σ₁)]))


(: no-stops : (-> Env Env))
(define (no-stops ξ)
  (for/hash : Env ([(nam trans) (in-hash ξ)]
                   #:unless (eq? trans 'Stop))
    (values nam trans)))

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
     (define-values (val ξ₁ Σ₄) (seval (parse (mark rhs scp-new) Σ₃) ξ ctx-e Σ₃))
     ;; Note: we drop the ξ₁ environment
     (define ξ-new (hash-set ξ nam-new val))
     (define stx-newbody (mark body scp-new))
     (define ctx-newe (set-add ctx-e scp-new))
     (sexpand stx-newbody ξ-new ctx-newe Σ₄)]

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
         ;; use-site scope.
         (define-values (scp-new Σ₃) (fresh-scope (Stx (Sym 'a) ∅) Σ₂))
         (define-values (exp ξ₁ Σ₄)
           ;; @mflatt: Should ctx-e have a new scope?
           (seval (App trans (list (mark (mark stx scp-orig) scp-new)))
                  ξ ctx-e Σ₃))
         ;; Note: we drop the ξ₁ environment
         (unless (Stx? exp) (error 'seval "Macro transformation produced non-syntax: ~a" exp))
         ;; Note: dropping ξ₁ environment
         (sexpand (mark exp scp-new) ξ (set-add ctx-e scp-orig) Σ₄)]
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
     ;; @mflatt: is this right?
     (define-values (done0 Σ₁) (sexpand stx0 ξ ctx-e Σ))
     (sexpand* (cons done0 done) stxs* ξ ctx-e Σ₁)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Mode (U 'flip 'add 'remove))
(: mode->op : (-> Mode (-> Ctx Scope Ctx)))
(define (mode->op mode)
  (case mode
    [(flip) (λ (ctx scp) (if (set-member? ctx scp)
                             (set-remove ctx scp)
                             (set-add ctx scp)))]
    [(add) (λ (ctx scp) (set-add ctx scp))]
    [(remove) (λ (ctx scp) (set-remove ctx scp))]))

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
    ;; Stx and Vdefs
    [else from]))

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
