#lang typed/racket
(require "common.rkt")
;; An address and a mrk are names.
(define-type Addr Name)
(define-type Mrk Name)

(struct Vdefs ([σ : Sigma]) #:transparent)
(define-type Val1 (U Fun Atom Stx Vdefs))
(define-type Val (U Val1 (Listof Val)))
(define-predicate val? Val)
(mk-Types [Stx stxs? S-Identifier s-identifier? s-identifiers? Ctx]
          [Var App Ast ast? Fun Val val?]
          δ)

(define-type Sigma (U Addr #f))

(struct -• () #:transparent) (define • (-•))
(struct Rename ([ctx : Ctx]
                [id : S-Identifier]
                [name : Name]
                [σ : Sigma]) #:transparent)
(struct Mark ([ctx : Ctx]
              [mrk : Mrk]) #:transparent)
(struct Defs ([ctx : Ctx]
              [σ : Sigma]) #:transparent)
(define-type Ctx (U -• Rename Mark Defs))

(define-type Resolution (HashTable S-Identifier Symbol))
(: empty-res : Resolution)
(define empty-res (hash))
(define-type DefCtxStore (HashTable Sigma Resolution))
(struct VarTrans ([id : S-Identifier]) #:transparent)
(define-type Transform (U 'Fun 'Let-Syntax 'Quote 'Stop VarTrans Val))
(define-type Env (HashTable Name Transform))

(define-type Gen (Listof Number))
(define-type mrk+gen (Pairof Mrk Gen))

(: seval : (-> Ast Env mrk+gen DefCtxStore (Values Val Env DefCtxStore)))
(define (seval ast ξ mrk Σ)
  (match ast
    [(App head args)
     (match head 
       [(Fun var body)
        (match args
          [(list arg)
           (define-values (val ξ₁ Σ₁) (seval arg ξ mrk Σ))
           (seval (subst body var val) ξ₁ mrk Σ₁)]
          [_ (error 'undefined-fn-args)])]
       [(? prim? prim)
        (define-values (vals ξ₁ Σ₁) (seval* '() args ξ mrk Σ))
        (values (δ prim vals) ξ₁ Σ₁)]

       ;; Model in paper has this after ast_op, but catch-all...?
       [(== lvalue eq?)
        (match args
          [(list arg)
           (define-values (stx-pre ξ₁ Σ₁) (seval arg ξ mrk Σ))
           (define stx (assert stx-pre Stx?))
           (define trans (hash-ref ξ (resolve stx Σ₁)
                                   (λ _ (error 'local-value "Unbound id: ~a" stx))))
           (unless (val? trans)
             (error 'seval "Local value not a value: ~a" trans))
           (values trans ξ₁ Σ₁)]
          [_ (error 'undefined-lvalue-args)])]

       [(== lexpand eq?)
        (match args
          [(list ast-expr ast-stops ast-defs)
           (match-define (cons mrk* gen) mrk)
           (define-values (stx-expr-pre ξ₁ Σ₁) (seval ast-expr ξ (cons mrk* (cons 0 gen)) Σ))
           (define stx-expr (assert stx-expr-pre Stx?))
           (define-values (stops-pre ξ₂ Σ₂) (seval ast-stops ξ₁ (cons mrk* (cons 1 gen)) Σ₁))
           (define stops (assert stops-pre s-identifiers?))
           (define-values (vd-pre ξ₃ Σ₃) (seval ast-defs ξ₂ (cons mrk* (cons 2 gen)) Σ₂))
           (match-define (Vdefs σ) vd-pre)
           (: ξ-stops : Env)
           (define ξ-stops
             (for/fold ([ξ-stops : Env (no-stops ξ₃)])
                 ([id-stop : S-Identifier (in-list stops)])
               (hash-set ξ-stops (resolve id-stop Σ₃) 'Stop)))
           (define stx-new (defs (mark stx-expr mrk*) σ))
           (define-values (stx Σ₄) (sexpand stx-new ξ-stops (cons 3 gen) Σ₃))
           (values (mark (defs stx σ) mrk*) ξ₃ Σ₄)])]

       [(== new-defs eq?)
        (match args
          ['()
           ;; Pun σ as the basis for the generated name
           (define σ (fresh-name (Stx (Sym 'σ) •) (cdr mrk)))
           (values (Vdefs σ) ξ (hash-set Σ σ empty-res))]
          [_ (error 'undefined-new-defs-args)])]

       [(== def-bind eq?)
        (match args
          [(list ast-defs ast-id)
           (match-define (cons mrk* gen) mrk)
           (match-define-values ((Vdefs σ) ξ₁ Σ₁)
                                (seval ast-defs ξ (cons mrk* (cons 0 gen)) Σ))
           (define-values (id-val ξ₂ Σ₂) (seval ast-id ξ₁ (cons mrk* (cons 1 gen)) Σ₁))
           (define id (assert id-val s-identifier?))
           ;; Defining id freshens it.
           (define nam-new (fresh-name id gen))
           (define id-new (rename id id nam-new))
           (define Σ₃ (store Σ₂ σ (mark id mrk*) nam-new))
           (values 0 (hash-set ξ nam-new (VarTrans id-new)) Σ₃)]

          ;; bind expand-time value in definition context
          [(list ast-defs ast-id ast-stx)
           (match-define (cons mrk* gen) mrk)
           (match-define-values ((Vdefs σ) ξ₁ Σ₁)
                                (seval ast-defs ξ (cons mrk* (cons 0 gen)) Σ))
           (define-values (id-val ξ₂ Σ₂)
             (seval ast-id ξ₁ (cons mrk* (cons 1 gen)) Σ₁))
           (define-values (stx-val ξ₃ Σ₃)
             (seval ast-stx ξ₂ (cons mrk* (cons 2 gen)) Σ₁))
           (define-values (val ξ₄ Σ₄)
             (seval (parse (defs (mark (assert stx-val Stx?) mrk*) σ) Σ₃)
                    ξ₃
                    (cons mrk* (cons 3 gen))
                    Σ₃))
           (define id (assert id-val s-identifier?))
           (define nam-new (fresh-name id gen))
           (define id-new (rename id id nam-new))
           (define Σ₅ (store Σ₄ σ (mark id mrk*) nam-new))
           (values 0 (hash-set ξ₄ nam-new val) Σ₅)])]

       [_ ;; head just an ast
        (define-values (head-e ξ₁ Σ₁) (seval head ξ mrk Σ))
        (seval (App head-e args) ξ₁ mrk Σ₁)])]
    [(? val? val) (values val ξ Σ)]))

(: seval* : (-> (Listof Val) (Listof Ast) Env mrk+gen DefCtxStore
                (Values (Listof Val) Env DefCtxStore)))
(define (seval* vals asts ξ mrk Σ)
  (match asts
    ['() (values (reverse vals) ξ Σ)]
    [(cons ast0 asts*)
     (define-values (val0 ξ₁ Σ₁) (seval ast0 ξ mrk Σ))
     (define-values (mrk* number0 gen)
       (match mrk
         [(cons mrk* (cons number0 gen)) (values mrk* number0 gen)]
         [_ (error 'seval* "Bad mark ~a" mrk)]))
     (define number1 (add1 number0))
     (seval* (cons val0 vals) asts* ξ₁ (cons mrk* (cons number1 gen)) Σ₁)]))

;; Give scope meaning to primitives
(: sexpand : (-> Stx Env Gen DefCtxStore (Values Stx DefCtxStore)))
(define (sexpand stx ξ gen Σ)
  (match-define (Stx a/los ctx) stx)

  (: application : (-> Stx (Listof Stx) (Values Stx DefCtxStore)))
  (define (application rtor rnd)
    (define-values (appform Σ₁)
      (sexpand* '() (cons rtor rnd) ξ (cons 0 gen) Σ))
    (values (Stx appform ctx) Σ₁))
  
  (match a/los
    ;; lambda
    [(list (? s-identifier? id-lam) (? s-identifier? id-arg) stx-body)
     #:when (eq? 'Fun (hash-ref ξ (resolve id-lam Σ) (λ _ (error 'expand "λ Unbound id: ~a" id-lam))))
     ;; For hygienic binding, we create a new name for the binder
     (define nam-new (fresh-name id-arg gen))
     ;; And rename it.
     (define id-new (rename id-arg id-arg nam-new))
     ;; And ensure the binder is renamed in the body.
     (define stx-newbody (rename stx-body id-arg nam-new))
     ;; And make references understand the name transform.
     (define ξ-new (hash-set ξ nam-new (VarTrans id-new)))
     ;; Then we continue expanding in the extended context.
     (define-values (stx-expbody Σ₁) (sexpand stx-newbody ξ-new (cons 0 gen) Σ))
     (values (Stx (list id-lam id-new stx-expbody) ctx) Σ₁)]

    ;; quote & syntax
    [(list (? s-identifier? id-quote) _)
     #:when (eq? 'Quote (hash-ref ξ (resolve id-quote Σ)
                                  (λ _ (error 'expand "' Unbound id: ~a" id-quote))))
     (values stx Σ)]

    ;; macro binding
    [(list (? s-identifier? id-ls) (? s-identifier? id-mac) rhs body)
     #:when (eq? 'Let-Syntax (hash-ref ξ (resolve id-ls Σ)
                                       (λ _ (error 'expand "let-syntax Unbound id: ~a" id-ls))))
     ;; Let-Syntax is another binding form, so we create a fresh name for the binder
     (define nam-new (fresh-name id-mac gen))
     ;; The right hand side is evaluated in phase 1
     (define-values (val ξ₁ Σ₁) (seval (parse rhs Σ) ξ (cons 'no-mrk (cons 0 gen)) Σ))
     ;; Note: we drop the ξ₁ environment
     ;; We rename the binder in the body and continue expanding with the
     ;; environment extended with the evaluated transformer.
     (define stx-newbody (rename body id-mac nam-new))
     (sexpand stx-newbody (hash-set ξ nam-new val) (cons 1 gen) Σ₁)]

    ;; (macro) application and stops
    [(cons head args)
     (cond
      [(s-identifier? head)
       (define trans (hash-ref ξ (resolve head Σ)
                               (λ _ (error 'expand "Application Unbound id: ~a" head))))
       (cond
        ;; macro application
        [(val? trans)
         (define mrk-new (fresh-name (Stx (Sym 'mrk) •) gen))
         (define-values (exp ξ₁ Σ₁)
           (seval (App trans (list (mark stx mrk-new))) ξ (cons mrk-new (cons 0 gen)) Σ))
         (unless (Stx? exp) (error 'seval "Macro transformation produced non-syntax: ~a" exp))
         ;; Note: dropping ξ₁ environment
         (sexpand (mark exp mrk-new) ξ (cons 1 gen) Σ₁)]
        [(eq? trans 'Stop)
         (values stx Σ)]
        [else (application head args)])]
      [else (application head args)])]

    ;; (Stx Sym _) is an identifier.
    [(? Sym?)
     (match (hash-ref ξ (resolve stx Σ) (λ _ (error 'expand "Reference Unbound id: ~a" stx)))
       [(VarTrans id-new) (values id-new Σ)]
       [bad (error 'sexpand "Bad reference: ~a" bad)])]

    [bad (error 'sexpand "Bad syntax: ~a" bad)]))

(: sexpand* : (-> (Listof Stx) (Listof Stx) Env Gen DefCtxStore (Values (Listof Stx) DefCtxStore)))
(define (sexpand* done stxs ξ gen Σ)
  (match stxs
    ['() (values (reverse done) Σ)]
    [(cons stx0 stxs*)
     (match gen
       [(cons num0 gen*)
        (define-values (done0 Σ₁) (sexpand stx0 ξ gen Σ))
        (sexpand* (cons done0 done) stxs* ξ (cons (add1 num0) gen) Σ₁)]
       [_ (error 'sexpand* "Expected non-empty gen")])]))

;; store expects σ to be in the domain of Σ
(: store : (-> DefCtxStore Sigma S-Identifier Name DefCtxStore))
(define (store Σ σ id name)
  (hash-set Σ σ (hash-set (hash-ref Σ σ) id name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: rename : (-> Stx Stx Name Stx))
(define (rename stx id nam)
  (match stx
    [(Stx (? atom? a) ctx)
     (Stx a (Rename ctx id nam #f))]
    [(Stx (? list? stxs) ctx)
     (Stx (for/list : (Listof Stx) ([stx : Stx (in-list stxs)]) (rename stx id nam))
          (Rename ctx id nam #f))]))

(: defs : (-> Stx Sigma Stx))
(define (defs stx σ)
  (match stx
    [(Stx (? atom? a) ctx)
     (Stx a (Defs ctx σ))]
    [(Stx (? list? stxs) ctx)
     (Stx (for/list : (Listof Stx) ([stx (in-list stxs)]) (defs stx σ)) (Defs ctx σ))]))

(: mark : (-> Stx Mrk Stx))
(define (mark stx mrk)
  (match stx
    [(Stx (? atom? a) ctx)
     (Stx a (Mark ctx mrk))]
    [(Stx (? list? stxs) ctx)
     (Stx (for/list : (Listof Stx) ([stx (in-list stxs)]) (mark stx mrk))
          (Mark ctx mrk))]))

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
    [(? Stx? stx) stx]
    [(? Vdefs? d) d]))

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
    [(Stx a/los ctx) (set-union (ctx-support ctx) (support a/los))]
    ;; Atom and Vdefs
    [_ (seteq)]))

(: ctx-support : (-> Ctx (Setof Name)))
(define (ctx-support ctx)
  (match ctx
    [(== • eq?) (seteq)]
    [(Rename ctx (Stx (Sym n) ctx*) name _)
     (set-union (ctx-support ctx) (ctx-support ctx*) (seteq n name))]
    ;; Marks and sigmas are separate name spaces (kinda). Never compared.
    [(Mark ctx _) (ctx-support ctx)]
    [(Defs ctx _) (ctx-support ctx)]))

(: support* : (-> (Setof Name) (Listof Ast) (Setof Name)))
(define (support* base lst)
  (for/fold ([S : (Setof Name) base])
      ([a (in-list lst)])
    (set-union S (support a))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: no-stops : (-> Env Env))
(define (no-stops ξ)
  (for/hash : Env ([(nam trans) (in-hash ξ)]
                   #:unless (eq? trans 'Stop))
    (values nam trans)))

(: resolve : (-> Stx DefCtxStore Name))
(define (resolve stx Σ) (resolve* stx Σ (set) (set)))

;; Resolves an identifier to a name; this is the heart of
;;  the syntax-object support for lexical scope
(: resolve* : (-> Stx DefCtxStore (Setof Sigma) (Setof Sigma) Name))
(define (resolve* id Σ spine branch)
  (match id
    [(Stx (Sym nam) ctx)
     (let loop ([nam nam] [ctx ctx] [Σ Σ] [spine spine] [branch branch])
       (match ctx
         [(== • eq?) nam]
         [(Mark ctx mrk) (loop nam ctx Σ spine branch)]
         [(Rename ctx id-orig nam* σ)
          (define nam1 (resolve* id-orig Σ branch branch))
          (cond
           [(and (eq? nam1 (loop nam ctx Σ (set-add spine σ) branch))
                 (equal? (marksof id-orig Σ nam1)
                         (marksof (Stx (Sym nam) ctx) Σ nam1)))
            nam*]
           [else (loop nam ctx Σ spine branch)])]
         [(Defs ctx σ)
          (cond
           [(set-member? spine σ)
            (loop nam ctx Σ spine branch)]
           [else
            (define store-val (hash-ref Σ σ (λ _ (error 'resolve "Unbound def: ~a" σ))))
            (define ctx-new (renames σ store-val ctx))
            (loop nam ctx-new Σ spine (set-add branch σ))])]))]
    [_ (error 'resolve* "Expected identifier")]))

(: renames : (-> Sigma Resolution Ctx Ctx))
(define (renames σ store-val ctx)
  (for/fold ([ctx : Ctx ctx])
      ([(id nam) (in-hash store-val)])
    (Rename ctx id nam σ)))

;; Mark "sets" are not actually sets.
;; This is a trixie bit that is a little broken and motivates "set of scopes"
(: marksof : (-> S-Identifier DefCtxStore Name (Listof Mrk)))
(define (marksof stx Σ nam)
  (let extract ([ctx (Stx-ctx stx)])
    (match ctx
      [(== • eq?) '()]
      [(Mark ctx mrk) (add-remove mrk (extract ctx))]
      [(Rename ctx id nam2 σ) (extract ctx)]
      [(Defs ctx σ)
       (if (in-range? (hash-ref Σ σ (λ _ (error 'marksof "Unbound def: ~a" σ))) nam)
           '()
           (extract ctx))])))

(: in-range? : (All (A B) (-> (HashTable A B) B Boolean)))
(define (in-range? h v)
  (for/or ([hv (in-hash-values h)]) (eq? v hv)))

;; Add or cancel a mark only at the head of a list of marks.
(: add-remove : (-> Mrk (Listof Mrk) (Listof Mrk)))
(define (add-remove mrk mrks)
  (match mrks
    ['() (list mrk)]
    [(cons mrk* mrks*)
     (if (eq? mrk mrk*)
         mrks*
         (cons mrk mrks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: fresh-name : (-> Stx Gen Name))
(define (fresh-name stx gen)
  (match stx
    [(Stx (Sym nam) ctx)
     (string->symbol (format "~a~a"
                             nam
                             (apply
                              string-append
                              (for/list : (Listof String) ([c (reverse gen)])
                                (format ":~a" c)))))]))

#|
;; Example:
 (lambda a
   (let-syntax thunk (lambda e [...] (Stx a •) [...])
    (thunk ('+ (Stx a •) '1))))
|#
(define-type Sexp (U Number Boolean String Symbol (Listof Sexp)))
(: sexp->stx : (-> Sexp Stx))
(define (sexp->stx sexp)
  (match sexp
    ['cons (Stx CONS •)]
    ['car (Stx CAR •)]
    ['cdr (Stx CDR •)]
    ['list (Stx LIST •)]
    ['stx-e (Stx stx-e •)]
    ['mk-stx (Stx mk-stx •)]
    ['+ (Stx PLUS •)]
    ['new-defs (Stx new-defs •)]
    ['def-bind (Stx def-bind •)]
    ['local-value (Stx lvalue •)]
    ['local-expand (Stx lexpand •)]
    [(? symbol? s) (Stx (Sym s) •)]
    [(? atom? a) (Stx a •)]
    [(? list? l) (Stx (map sexp->stx l) •)]))

(: ex0 : Stx)
(define ex0
  (sexp->stx
   '(lambda a
      (let-syntax thunk (lambda e
                          ('mk-stx
                           ('list
                            (syntax lambda)
                            (syntax dummy)
                            ('car ('cdr ('stx-e e))))
                           e))
                  (thunk ('+ a '1))))))

(: ξ₀ : Env)
(define ξ₀ (make-immutable-hash
            (list
             (cons 'lambda 'Fun)
             (cons 'let-syntax 'Let-Syntax)
             (cons 'quote 'Quote)
             (cons 'syntax 'Quote))))
(: gen₀ : Gen)
(define gen₀ '())
(: Σ₀ : DefCtxStore)
(define Σ₀ (hash))

(let-values ([(stx Σ) (sexpand ex0 ξ₀ gen₀ Σ₀)])
  (parse stx Σ))
