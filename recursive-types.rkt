#lang racket

(module+ test (require rackunit))
;; Interpreter for the GTLC + nats,tuples,recursive types

(define base-types '(() Nat Bool))

(define (base-type? x) (set-member? base-types x))

(define type-keywords `(? μ -> . ,base-types))

(define (type-keyword? x)
  (set-member? type-keywords x))

(define (type-variable? x)
  (and (symbol? x) (not (type-keyword? x))))


(struct μ ([ref #:mutable])
  #:transparent)

(define-syntax-rule (-μ x t/c)
  (let ([x (μ (void))])
    (set-μ-ref! x t/c)
    x))

;; Type Syntax
(define (type? x [valid (set)] [pending (set)] [seen (set)])
  (define (rec/pending x v s)
    (type? x valid (set-add pending v) (set-add seen s)))
  (define (rec/valid x)
    (type? x (set-union valid pending) (set) seen))
  (match x
    [`(μ ,(? type-variable? x0) ,x1)
     (rec/pending x1 x0 x)]
    [(? type-variable? x)
     (set-member? valid x)]
    ['Nat #t]
    [(or (? base-type?)
         '?
         `#(,(? rec/valid) ,(? rec/valid))
         `(,(? rec/valid) -> ,(? rec/valid)))
     #t]
    [(μ x0)
     (or (set-member? seen x)
         ;; Here we clear the other two sets to "enforce"
         ;; once we are using refs you can't use type-variables
         (type? x0 (set) (set) (set-add x)))]))

(define (type->cyclic-type t)
  (let c ([t t] [env (hash)])
    (match t
      [(or (? base-type?) '?) t]
      [`#(,t0 ,t1) `#(,(c t0 env) ,(c t1 env))]
      [`(,t0 -> ,t1) `(,(c t0 env) -> ,(c t1 env))]
      [(? type-variable? X) (hash-ref env X)]
      [`(μ ,X ,t0) (-μ x (c t0 (hash-set env X x)))])))

;; substitute type s for variable x in type t
(define (type-subst t x s)
  (let rec ([t t])
    (match t
      [(? type-variable? v) #:when (eq? v x) s]
      [(vector t0 t1) (vector (rec t0) (rec t1))]
      [`(,t0 -> ,t1) `(,(rec t0) -> ,(rec t1))]
      [`(μ ,v ,t0) #:when (not (eq? v x)) `(μ ,v ,(rec t0))]
      [_ t])))

(define (unfold t)
  (match t
    [`(μ ,x ,t0) (type-subst t0 x t)]
    [(μ t0)
     (error 'unfold "can't be used on cyclic types")]
    [_ (error 'fold "can only be used on recursive-types")]))

(module+ test
  (define-syntax-rule (t-type? t)
    (test-pred (~a 't) type? t))
  (t-type? 'Nat)
  (define natXnat #(Nat Nat))
  (t-type? natXnat)
  (define nat->nat '(Nat -> Nat))
  (t-type? nat->nat)
  (define Hungry-Type '(μ H (Nat -> H)))
  (t-type? Hungry-Type)
  (define Stream-Type '(μ S #(Nat (() -> S))))
  (t-type? Stream-Type)
  (define Other-Stream-Type '(μ S2 (() -> #(Nat S2))))
  (t-type? Other-Stream-Type)
  (define Dyn-Other-Stream-Type '(μ S2 (() -> #(? S2))))
  (t-type? Dyn-Other-Stream-Type))

(define (subtype-aux subtype?)
  ;; Defined this way to easily override the behavior
  (lambda  (Γ A S T)
    ;; Γ (Gamma) is a lexical substitution of mu bindings
    ;; A is a cache of previous subtyping queries
    ;; subtype-aux returns a substitution if S is a subtype of T
    ;; otherwise it returns #f
    (match* (S T)
      ;; If A is fails then we have already failed
      [(_ _) #:when (not A) #f]
      ;; If A contains the pair then we have already checked that
      ;; S is a subtype of T
      [(_ _) #:when (set-member? A (cons S T)) A]
      [(T T) A]
      [((? symbol? X) _) (=> continue)
       (define v? (hash-ref Γ X))
       (cond
         [v? (subtype? Γ A v? T)]
         [else (continue)])]
      [(_ (? symbol? X)) (=> continue)
       (define v? (hash-ref Γ X))
       (cond
         [v? (subtype? Γ A S v?)]
         [else (continue)])]
      [((vector S1 S2) (vector T1 T2))
       ;; Covarient for tuples
       (define A0 (subtype? Γ A S1 T1))
       (subtype? Γ A0 S2 T2)]
      [(`(,S1 -> ,S2) `(,T1 -> ,T2))
       ;; Contravarient for functions
       (define A0 (subtype? Γ A T1 S1))
       (subtype? Γ A0 S2 T2)]
      [(_ _)
       (define A0 (set-add A (cons S T)))
       (match* (S T)
         [(`(μ ,X ,S1) T) (subtype? (hash-set Γ X S) A0 S1 T)]
         [(S `(μ ,X ,T1)) (subtype? (hash-set Γ X T) A0 S T1)]
         [((μ S0) T) (subtype? Γ A0 S0 T)]
         [(S (μ T0)) (subtype? Γ A0 S T0)]
         [(_ _) #f])])))

(define (subtype? S T)
  (define (st? Γ A S T) ((subtype-aux st?) Γ A S T))
  (st? (hash) (set) S T))

(define (consistent-subtype? S T)
  (define (st? Γ A S T)
    (match* (S T)
      [('? _) A]
      [(_ '?) A]
      [(_ _) ((subtype-aux st?) Γ A S T)]))
  (st? (hash) (set) S T))

(module+ test
  (define-syntax-rule (t-st S T)
    (let ([s S] [t T])
      (unless (type? s)
        (error 'todo))
      (unless (type? t)
        (error 'todo))
      (test-not-false (~a '(subtype? S T)) (subtype? s t))))
  (define-syntax-rule (t-cst S T)
    (let ([s S] [t T])
      (unless (type? s)
        (error 'todo))
      (unless (type? t)
        (error 'todo))
      (test-not-false (~a '(consistent-subtype? S T))
                      (consistent-subtype? s t))))
  (t-st 'Nat 'Nat)
  (t-cst 'Nat 'Nat)
  (t-st '(μ X #(Nat X)) '(μ Y #(Nat Y)))
  (t-cst '(μ X #(? X)) '(μ Y #(Nat Y)))
  (t-cst Other-Stream-Type Dyn-Other-Stream-Type)
  (t-cst Dyn-Other-Stream-Type Other-Stream-Type))

(define-syntax-rule (match? e p ...)
  (match e [p #t]  ... [_ #f]))


(define (keyword? x) (set-member? keywords x))

(define (variable? x) (and (symbol? x) (not (keyword? x))))

;; Syntax
(define (expr? x)
  (match? x
    '()
    `(λ (,(? variable?) : ,(? type?)) : ,(? type?) ,(? expr?))
    `(let ([,(? variable?) ,(? expr?)]) ,(? expr?))
    (? variable?)
    `(,(? expr?) ,(? expr?))
    (? exact-nonnegative-integer?)
    `(+ ,(? expr?) ,(? expr?))
    `(- ,(? expr?) ,(? expr?))
    `(= ,(? expr?) ,(? expr?))
    `(? boolean?)
    `(if ,(? expr?) ,(? expr?) ,(? expr?))
    (? vector? (app vector-length 2))
    `(,(? expr?) . ,(or 0 1))
    `(ann ,(? expr?) ,(? type?))))

;; A program is a series of definitions followed by an expression
(define (prgm? x)
  (match? x
    `((define ,(? variable?) : ,(? type?) ,(? expr?))
      ...
      ,(? expr?))))

(define-syntax-rule (invalid expect got)
  (error 'invalid-syntax "expected ~a got ~a" expect got))

(define (assert-prgm! x)
  (define (assert-variable! x)
    (unless (variable? x)
      (invalid 'symbol x)))
  (define (assert-type! x)
    (unless (type? x)
      (invalid 'type x)))
  (define (assert-expr! x)
    (match x
      ['() (void)]
      [`(λ (,x : ,t0) : ,t1 ,e)
       (assert-variable! x)
       (assert-type! t0)
       (assert-type! t1)
       (assert-expr! e)]
      [`(λ (,x : ,t0) ,e)
       (assert-variable! x)
       (assert-type! t0)
       (assert-expr! e)]
      [`(let ([,x ,e0]) ,e1)
       (assert-variable! x)
       (assert-expr! e0)
       (assert-expr! e1)]
      [(? variable?) (void)]
      [`(,e0 ,e1)
       (assert-expr! e0)
       (assert-expr! e1)]
      [(? exact-nonnegative-integer?) (void)]
      [`(,(? binop?) ,e0 ,e1)
       (assert-expr! e0)
       (assert-expr! e1)]
      [`(? boolean?) (void)]
      [`(if ,e0 ,e1 ,e2)
       (assert-expr! e0)
       (assert-expr! e1)
       (assert-expr! e2)]
      [`#(,e0 ,e1)
       (assert-expr! e0)
       (assert-expr! e1)]
      [`(,e . ,(or 0 1))
       (assert-expr! e)]
      [`(ann ,e ,t)
       (assert-expr! e)
       (assert-type! t)]
      [_ (invalid 'expression x)]))
  (define (assert-define! x)
    (match x
      [`(define ,s : ,t ,e)
       (unless (symbol? s) (invalid 'symbol s))
       (unless (type? t) (invalid 'type t))
       (assert-expr! e)]
      [_ (invalid 'define x)]))
  (match x
    [`(,d* ... ,e)
     (for ([d d*]) (assert-define! d))
     (unless (expr? e)
       (invalid 'expression e))]
    [_ (invalid 'program x)]))



(module+ test
  (define e0 `(+ 40 (+ 1 1)))
  (test-pred "expression 0" expr? e0)
  (define e0.5 `(+ x 1))
  (test-pred "expression 0.5" expr? e0.5)
  (define e1 `(λ (x : Nat) : Nat ,e0.5))
  (test-pred "expression 1" expr? e1)
  (define add1-41 '(add1 41))
  (test-pred "add1 to 41" expr? add1-41)
  
  (define p0 `(,e0))
  (test-pred "program 0" prgm? p0)
  (define p1
    `((define add1 : ,nat->nat ,e1)
      ,add1-41))
  (test-pred "program 1" prgm? p1)

  (define fst-ones '((ones ()) . 0))
  (test-pred "first of ones" expr? fst-ones)
  (define oneXones #(1 ones))
  (test-pred "1 and ones" expr? oneXones)
  (define ones-lambda `(λ (_ : ()) : (μ S #(Nat (() -> S))) #(1 ones)))
  (test-pred "ones lambda" expr? ones-lambda)
  
  (define p2
    `((define ones : ,Other-Stream-Type ,ones-lambda)
      ,fst-ones))
  (test-pred "program 2" prgm? p2)

  (define stream-ref-base `((s ()) . 0))
  (test-pred "sr base" expr? stream-ref-base)
  (define stream-ref-ind `((stream-ref ((s ()) . 1)) (- x 1)))
  (test-pred "sr ind" expr? stream-ref-ind)
  (define stream-ref-cond `(= x 0))
  (test-pred "sr cond" expr? stream-ref-cond)
  (define stream-ref-if
    `(if (= x 0)
         ((s ()) . 0)
         ((stream-ref ((s ()) . 1)) (- x 1))))
  (test-pred "sr if" expr? stream-ref-if)
  (define stream-ref-body
    `(λ (x : Nat) : ? ,stream-ref-if))
  (test-pred "sr body" expr? stream-ref-body)
  (define stream-ref-lam
    `(λ (s : ,Dyn-Other-Stream-Type)
      : (Nat -> ?)
      ,stream-ref-body))
  (test-pred "expression stream-ref" expr? stream-ref-lam)

  (define p3-main `(+ ((stream-ref dones) 4) 41))
  (test-pred "p3 main" expr? p3-main)
  (define p3
    `((define ones : (μ S2 (() -> #(Nat S2)))
        (λ (_ : ()) : (μ S #(Nat (() -> S)))
           #(1 ones)))
      (define dones : (μ S2 (() -> #(? S2)))
        ones)
      (define stream-ref : ((μ S2 (() -> #(? S2))) -> (Nat -> ?))
        (λ (s : (μ S2 (() -> #(? S2))))
          : (Nat -> ?)
          (λ (x : Nat) : ?
             (if (= x 0)
                 ((s ()) . 0)
                 ((stream-ref ((s ()) . 1))
                  (- x 1))))))
      (+ ((stream-ref dones) 4) 41)))
  
  (test-pred "program 3" prgm? p3))


(define (unique? xs)
  (not (check-duplicates xs)))

(define ((error-th x))
  (error 'type-check "unbound variable: ~a" x))

(define-syntax (raise-not-consistent-subtype stx)
  (syntax-case stx ()
    [(_ e s t)
     #'(error 'type-check "~a : ~a ¬⊆ ~a" e s t)]
    [(_ s t)
     #'(error 'type-check "~a ¬⊂ ~a" s t)]))

(define (insert-cast e t1 t2)
  (if (equal? t1 t2)
      e
      `(cast ,e ,t1 ,t2)))

(define (sub n m)
  (define p (- n m))
  (if (< p 0)
      0
      p))

(define binops
  (make-immutable-hash
   `((+ (Nat Nat -> Nat)  ,+)
     (- (Nat Nat -> Nat)  ,sub)
     (= (Nat Nat -> Bool) ,=)
     (% (Nat Nat -> Nat)  ,modulo))))

(define keywords '(λ let . (hash-keys binops)))

(define (truthy? x) (not (not x)))

(define (binop? x) (truthy? (hash-ref binops x #f)))

(define (binop-type x)
  (define entry? (hash-ref binops x))
  (unless entry?
    (error 'binop-type "~a not found" x))
  (list-ref entry? 0))

(define (binop->racket x)
  (define entry? (hash-ref binops x))
  (unless entry?
    (error 'binop->racket "~a not found" x))
  (list-ref entry? 1))

(define (assert-consistent-subtype! e t1 t2)
  (unless (consistent-subtype? t1 t2)
    (raise-not-consistent-subtype e t1 t2)))

(define (join S T [env (hash)])
  (match* (S T)
    [(t t) t]
    [('? t) t]
    [(t '?) t]
    ;; Don't Unfold Recursive types if you don't have to
    [(`(μ ,X ,S0) `(μ ,Y ,T0))
     `(μ ,X ,(join S0 T0 (hash-set env X Y)))]
    [((? type-variable? X) (? type-variable? Y))
     (unless (eq? X (hash-ref env Y))
       (raise-not-consistent-subtype X Y))
     X]
    [(`(μ ,_ ,_) _) (join (unfold S) T)]
    [(_ `(μ ,_ ,_)) (join S (unfold T))]
    [(`(,S0 -> ,S1) `(,T0 -> ,T1))
     `(,(join S0 T0) -> ,(join S1 T1))]
    [(`#(,S0 ,S1) `#(,T0 ,T1))
     `#(,(join S0 T0) ,(join S1 T1))]
    [(_ _) (raise-not-consistent-subtype S T)]))

;; type-synthesis : env, expr -> cc-expr, type
(define (synth Γ e)
  (let rec ([e e])
    (match e
      [(? variable? x)
       (define tₓ (hash-ref Γ x (error-th x)))
       (values x tₓ)]
      [`(λ (,x : ,tₓ) : ,tₘ ,m)
       (define m0 (check (hash-set Γ x tₓ) tₘ m))
       (values `(λ (,x : ,tₓ) : ,tₘ ,m0) `(,tₓ -> ,tₘ))]
      [`(λ (,x : ,tₓ) ,m)
       (define-values (m0 tₘ) (synth (hash-set Γ x tₓ) m))
       (values `(λ (,x : ,tₓ) : ,tₘ ,m0) `(,tₓ -> ,tₘ))]
      [`(let ([,x ,eₓ]) ,m)
       (define-values (eₑ tₓ) (synth Γ eₓ))
       (define-values (eₘ tₘ) (synth (hash-set Γ x tₓ) m))
       (values `(let ([,x ,eₑ]) ,eₘ) tₘ)]
      [`(,p ,a)
       (define-values (p0 tₚ) (rec p))
       (assert-consistent-subtype! p tₚ '(? -> ?))
       (match-define `(,tₐ -> ,tᵣ)
         (let loop ([tₚ tₚ])
           (match tₚ
             [`(,_ -> ,_) tₚ]
             ['?          `(? -> ?)]
             [`(μ ,x ,t) (loop (unfold tₚ))])))
       (define p1 (insert-cast p0 tₚ `(,tₐ -> ,tᵣ)))
       (define a0 (check Γ tₐ a))
       (values `(,p1 ,a0) tᵣ)]
      [(? exact-nonnegative-integer? n)
       (values n 'Nat)]
      [(list (? binop? op) a b)
       (match-define `(,A ,B -> ,C) (binop-type op))
       (define a0 (check Γ A a))
       (define b0 (check Γ B b))
       (values `(+ ,a0 ,b0) C)]
      [(? boolean? b)
       (values b 'Bool)]
      [`(if ,(app (curry check Γ 'Bool) c) ,(app rec e0 t0) ,(app rec e1 t1))
       (define t2 (join t0 t1))
       (define e2 (insert-cast e0 t0 t2))
       (define e3 (insert-cast e1 t1 t2))
       (values `(if ,c ,e2 ,e3) t2)]
      [`#(,(app rec e0 t0) ,(app rec e1 t1))
       (values `#(,e0 ,e1) `#(,t0 ,t1))]
      [(cons m (and i (or 0 1)))
       (define-values (m0 tₘ) (rec m))
       (assert-consistent-subtype! m tₘ #(? ?))
       (match-define tᵥ
         (let loop ([tₘ tₘ])
           (match tₘ
             [`#(,_ ,_) tₘ]
             ['? #(? ?)]
             [`(μ ,x ,t) (loop (unfold x t))])))
       (define tᵢ (vector-ref tᵥ i))
       (define m1 (insert-cast m0 tₘ tᵥ))
       (values `(,m1 . ,i) tᵢ)]
      ['() (values '() '())]
      [`(ann ,e ,t) (values (check Γ t e) t)])))


;; type-check : env, expr, type -> expr
(define (check Γ t e)
  (define-values (e0 tₑ) (synth Γ e))
  (assert-consistent-subtype! e tₑ t)
  (insert-cast e0 tₑ t))

(define (type-check prgm)
  (assert-prgm! prgm)
  (match prgm
    [`((define ,s* : ,t* ,e*) ... ,e)
     (unless (unique? s*)
       (error 'type-check-prgm
              "duplicate binding ~a"
              (check-duplicates s*)))
     (for ([t t*]) (type? t))
     (define rec-env (make-immutable-hash (map cons s* t*)))
     (define d*0
       (for/list ([s s*] [t t*] [e e*]) 
         `(define ,s : ,t ,(check rec-env t e))))
     (define-values (e0 _) (synth rec-env e))
     (append d*0 `(,e0))]))

(module+ test
  (check-not-exn (lambda () (type-check p1)))
  (check-not-exn (lambda () (type-check p2)))
  (check-not-exn (lambda () (type-check p3))))


(define ((env-lookup tl-env) env x)
  ;; Monadic use of or
  (or (hash-ref env x #f)
      (hash-ref tl-env x #f)
      (error 'undefined "~a" x)))


(define (cast v s t)
  (match* (s t)
    [(t t) v]
    [('? t) (cast (car v) (cdr v) t)]
    [(s '?) (cons v s)]
    [(`(μ ,_ ,_) t) (cast v (unfold s) t)]
    [(s `(μ ,_ ,_)) (cast v s (unfold t))]
    [((μ s0) t) (cast v s0 t)]
    [(s (μ t0)) (cast v s t0)]
    [(`(,s1 -> ,s2) `(,t1 -> ,t2))
     (lambda (x) (cast (v (cast x t1 s1)) s2 t2))]
    [(`#(,s1 ,s2) `#(,t1 ,t2))
     (match-define `#(,v1 ,v2) v)
     `#(,(cast v1 s1 t1) ,(cast v2 s2 t2))]))

(define ((eval cast coerce) e tl-env)
  (define lookup (env-lookup tl-env))
  (let eval ([e e] [env (hash)])
    (match e
      [(? variable? x) (lookup env x)]
      [(and v (or (? boolean?) (? number?) '())) v]
      [`(λ (,x : ,_) : ,_ ,m)
       (λ (a) (eval m (hash-set env x a)))]
      [`(let ([,x ,eₓ]) ,m)
       (let ([v (eval eₓ env)])
         (eval m (hash-set env x v)))]
      [`(,p ,a) ((eval p env) (eval a env))]
      [(list (? binop? op) a b)
       ((binop->racket op) (eval a env) (eval b env))]
      [`(if ,c ,e0 ,e1)
       (if (eval c env) (eval e0 env) (eval e1 env))]
      [`#(,e0 ,e1)
       (vector (eval e0 env) (eval e1 env))]
      [(cons m (and i (or 0 1)))
       (vector-ref (eval m env) i)]
      [`(cast ,e ,t1 ,t2)
       (cast (eval e env) t1 t2)]
      [`(coerce ,e ,c)
       (coerce (eval e env) c)])))


(define ((evaluate type-check compile eval) prgm)
  (match (compile (type-check prgm))
    [`((define ,v* : ,_ ,e*) ... ,e)
     (define tl-env (make-hash '()))
     (for ([v v*] [e e*])
       (hash-set! tl-env v (eval e tl-env)))
     (eval e tl-env)]
    [`(,d ... ,e)
     (for/list ([d d])
       (unless (match? d `(define ,v : ,_ ,e))
         (error 'internal-error "~a produced by type-checker" d)))]))

(define ((unexpected x) . a)
  (error 'unexpected "~a" `(,x . ,a)))


(define ((fold-expr f-expr) expr)
  (let m ([e expr])
    (match e
      [(and v (or (? variable?)
                  (? boolean?)
                  (? number?)
                  '()))
       (f-expr v)]
      [`(λ (,x : ,t0) : ,t1 ,e0)
       (f-expr `(λ (,x : ,t0) : ,t1 ,(m e0)))]
      [`(,e0 ,e1) (f-expr `(,(m e0) ,(m e1)))]
      [`(,(? binop? op) ,e0 ,e1) (f-expr `(,op ,(m e0) ,(m e1)))]
      [`(if ,e0 ,e1 ,e2) (f-expr `(if ,(m e0) ,(m e1) ,(m e2)))]
      [`#(,e0 ,e1) (f-expr `#(,(m e0) ,(m e1)))]
      [(cons e0 (and i (or 0 1))) (cons (m e0) i)]
      [`(cast ,e0 ,t0 ,t1) (f-expr `(cast ,(m e0) ,t0 ,t1))])))

(define ((map-prgm f-expr f-type) prgm)
  (match-define `((define ,s* : ,t* ,e*) ... ,e) prgm)
  (append
   (for/list ([s s*] [t t*] [e e*])
     `(define ,s : ,(f-type t) ,(f-expr e)))
   (list (f-expr e))))

(define prgm-identity values)

(define (compile-expr-types f-type)
  (fold-expr
   (lambda (e)
     (match e
       [`(cast ,e0 ,t0 ,t1)
        `(cast ,e0 ,(f-type t0) ,(f-type t1))]
       [`(λ (,x : ,t0) : ,t1 ,e0)
        `(λ (,x : ,(f-type t0)) : ,(f-type t1) ,e0)]
       [e e]))))

(define (compile-prgm-types f-type)
  (map-prgm (compile-expr-types f-type) f-type))

(module+ test
  (define types->etypes (compile-prgm-types type->cyclic-type))

  (define evaluate/cast
    (evaluate type-check prgm-identity (eval cast (unexpected 'coerce))))

  (define evaluate/ecast
    (evaluate type-check types->etypes (eval cast (unexpected 'coerce))))

  (test-not-exn "eval p3 cast" (thunk (evaluate/cast p3)))
  (test-not-exn "eval p3 ecast" (thunk (evaluate/ecast p3))))

;; <(μ X #(Int X) => (μ Y #(Dyn X))> = (μ X #(Int! X))
;; <(μ X #(Int X)) => #(Dyn (μ X #(Int X)))> = unfold ; #(Int! id)
;; (μ X #(Int X)):#(Int (μ X #(Int X)))|#(Int (μ X #(Int X))) #(Dyn (μ X #(Int X)))
;; <#(Dyn (μ X #(Int X))) => (μ X #(Int X))> = #(Int? id); fold
;; <(μ X (μ Y #(X Y))) => (μ X (μ Y #(? Y)))> = ...
;;                              (μ X (μ Y #((μ X (μ Y #(? Y)))? Y)

;;
(define (make-coercion s t)
  (define-values (c _)
    (let mc ([s s] [t t] [env (hash)])
    ;; This should be possible to only perform at
    ;; variable nodes once we go to graphs
    (define p (cons s t))
    (define ref? (hash-ref env p #f))
    (match ref?
      [(box _)
       (unless (unbox ref?)
         (set-box! ref? (gensym)))
       (values (unbox ref?) #t)]
      [(μ _)
       (set-μ-ref! ref? #t)
       (values ref? #t)]
      [_
       (match* (s t)
         [(t t)  (values `id #t)]
         [('? t) (values `(Seq (? ,t) id) #f)]
         [(t '?) (values `(Seq id (! ,t)) #f)]
         [(`(μ ,X ,s0) t)
          (define ref (box #f))
          (define env0 (hash-set env p ref))
          (define s1 (unfold s))
          (define-values (r id?) (mc s1 t env0))
          (define used-sym? (unbox ref))
          (cond
            [id? (values 'id #t)]
            [used-sym? (values `(μ ,used-sym? ,r) #f)]
            [else (values r #f)])]
         [(s `(μ ,Y ,t0))
          (define ref (box #f))
          (define env0 (hash-set env p ref))
          (define t1 (unfold t))
          (define-values (r id?) (mc s t1 env0))
          (define used-sym? (unbox ref))
          (cond
            [id? (values 'id #t)]
            [used-sym? (values `(μ ,used-sym? ,r) #f)]
            [else (values r #f)])]
         [((μ s0) t)
          (define var/mu (μ #f))
          (define env0 (hash-set env p var/mu))
          (define-values (r id?) (mc s0 t env0))
          (define used? (μ-ref var/mu))
          (cond
            [id?   (values 'id #t)]
            [used?
             (set-μ-ref! var/mu r)
             (values var/mu #f)]
            [else
             (values r #f)])]
         [(s (μ t0))
          (define var/mu (μ #f))
          (define env0 (hash-set env p var/mu))
          (define-values (r id?) (mc s t0 env0))
          (define used? (μ-ref var/mu))
          (cond
            [id?   (values 'id #t)]
            [used?
             (set-μ-ref! var/mu r)
             (values var/mu #f)]
            [else
             (values r #f)])]
         [(`(,s0 -> ,s1) `(,t0 -> ,t1))
          (define-values (r0 i0?) (mc t0 s0 env))
          (define-values (r1 i1?) (mc s1 t1 env))
          (values
           (match* (r0 r1)
             [('id 'id) 'id]
             [(_ _) `(,r0 -> ,r1)])
           (and i0? i1?))]
         [(`#(,s0 ,s1) `#(,t0 ,t1))
          (define-values (r0 i0?) (mc s0 t0 env))
          (define-values (r1 i1?) (mc s1 t1 env))
          (values
           (match* (r0 r1)
             [('id 'id) 'id]
             [(_ _) `#(,r0 ,r1)])
           (and i0? i1?))]
         [(other wise)
          (printf "fail:\n~a\n~a\n~a\n" s t env)
          (values 'fail #f)])])))
  c)

(define (coercion-α=? x y)
  (let rec ([x x] [y y] [ex (hash)] [ey (hash)])
    (match* (x y)
      [(x x) #t]
      [(`(μ ,x ,x0) `(μ ,y ,x1))
       (define g (gensym))
       (rec x0 x1 (hash-set ex x g) (hash-set ey y g))]
      [(`(,x0 -> ,x1) `(,y0 -> ,y1))
       (and (rec x0 y0 ex ey)
            (rec x1 y1 ex ey))]
      [(`#(,x0 ,x1) `#(,y0 ,y1))
       (and (rec x0 y0 ex ey)
            (rec x1 y1 ex ey))]
      [(`(Seq ,x0 ,x1) `(Seq ,y0 ,y1))
       (and (rec x0 y0 ex ey)
            (rec x1 y1 ex ey))]
      [(x y)
       (define x? (hash-ref ex x #f))
       (define y? (hash-ref ey y #f))
       (and x? y? (eq? x? y?))])))


(define ((check-α=? x) y) (coercion-α=? x y))

(module+ test
  (test-true "sc 1" (coercion-α=? 'Nat 'Nat))
  (test-true "sc 2" (coercion-α=? '(μ x x) '(μ y y)))
  (test-true "sc 3" (coercion-α=? '(μ x #((? Int) x)) '(μ y #((? Int) y))))

  (define sc4 (let ([x (μ (void))]) (set-μ-ref! x x)))
  (define sc5 (let ([x (μ (void))]) (set-μ-ref! x x)))
  (test-true "sc 4 5" (coercion-α=? sc4 sc5)))


(module+ test
  (test-equal? "make-crcn sanity" (make-coercion 'Nat 'Nat) 'id)
  

  (test-pred "make-crcn mu"
             (check-α=? '(μ X #((Seq (? Int) id) X))) 
             (make-coercion '(μ X #(? X)) '(μ Y #(Int Y))))

  (test-pred "make-crcn mu cyclic"
             (check-α=? (-μ X `#((Seq (? Int) id) ,X))) 
             (make-coercion (-μ X `#(? ,X))
                            (-μ Y `#(Int ,Y))))
    
  (test-pred "make-crcn fold"
             (check-α=? 'id)
             (make-coercion `#(Int ,(-μ X `#(Int ,X))) (-μ Y `#(Int ,Y))))

  (test-pred "make-crcn unfold"
             (check-α=? 'id)
             (make-coercion (-μ Y `#(Int ,Y))
                            `#(Int ,(-μ X `#(Int ,X)))))

  
  (test-pred "make-crcn project fold"
             (check-α=? '#((Seq (? Int) id) id))
             (make-coercion '#(? (μ X #(Int X))) '(μ Y #(Int Y))))

  (test-pred "make-crcn inject unfold"
             (check-α=? '#((Seq id (! Int)) id))
             (make-coercion '(μ Y #(Int Y)) '#(? (μ X #(Int X)))))

  (test-pred "make-crcn project unfold stream"
             (check-α=? '#((Seq (? Int) id) id))
             (make-coercion '(μ Y #(? (() -> Y)))
                            '#(Int (() -> (μ X #(? (() -> X)))))))

  (test-pred "make-crcn project unfold stream"
             (check-α=? '#(id (id -> (μ Y #((Seq (? Int) id) (id -> Y))))))
             (make-coercion '(μ Y #(? (() -> Y)))
                            '#(? (() -> (μ X #(Int (() -> X))))))))
  

(define ((cast->coercion compile-type) prgm)
  (define (c->c e)
    (match e
      [(and v (or (? variable?)
                  (? boolean?)
                  (? number?)
                  '()))
       v]
      [`(λ (,x : ,t0) : ,t1 ,m)
       `(λ (,x : ,(compile-type t0))
          : ,(compile-type t1)
          ,(c->c m))]
      [`(,p ,a)
       `(,(c->c p) ,(c->c a))]
      [`(,(? binop? op) ,a ,b)
       `(,op ,(c->c a) ,(c->c b))]
      [`(if ,c ,e0 ,e1)
       `(if ,(c->c c) ,(c->c e0) ,(c->c e1))]
      [`#(,e0 ,e1)
       `#(,(c->c e0) ,(c->c e1))]
      [(cons m (and i (or 0 1)))
       (cons (c->c m) i)]
      [`(cast ,e ,t1 ,t2)
       `(coerce ,(c->c e)
                ,(make-coercion (compile-type t1)
                                (compile-type t2)))]))
  (match-define `((define ,s* : ,t* ,e*) ... ,e) prgm)
  (append
   (for/list ([s s*] [t t*] [e e*])
     `(define ,s : ,(compile-type t) ,(c->c e)))
   (list (c->c e))))


;; Approaches ignore coercions in casts an
(define (coercion? x)
  (match? x
    `id
    `(? ,(? type?))
    `(! ,(? type?))
    `#(,(? coercion?) ,(? coercion?))
    `(,(? coercion?) -> ,(? coercion?))))

(struct hybrid-proxy (closure coercion)
  #:transparent
  #:property prop:procedure
  (lambda (p a)
    (define f (hybrid-proxy-closure p))
    (match-define `(,c0 -> ,c1) (hybrid-proxy-coercion p))
    (apply-coercion (f (apply-coercion a c0)) c1)))

(define (apply-coercion v c)
  (define ac apply-coercion)
  (define mc make-coercion)
  (define cc compose-coercions)
  (match c
    [`id
     v]
    [`(Seq ,c0 ,c1)
     (ac (ac v c0) c1)]
    [`(? ,t1)
     (match-define `(,v0 : ,t0) v)
     (ac v0 (mc t0 t1))]
    [`(! ,t0)
     `(,v : ,t0)]
    [`#(,c0 ,c1)
     (match-define `#(,v0 ,v1) v)
     `#(,(ac v0 c0) ,(ac v1 c1))]
    [`(,_ -> ,_)
     (cond
       [(hybrid-proxy? v)
        (define v0 (hybrid-proxy-closure v))
        (define c0 (hybrid-proxy-coercion v))
        (define c1 (cc c0 c))
        (ac v0 c1)]
       [else (hybrid-proxy v c)])]
    [`(μ ,X ,c0) (ac v (unfold c))]
    [(μ c0) (ac v c0)]))

(define (compose-coercions c d)
  (define mc make-coercion)
  ;; id? variables means "does the computational content
  ;; a variable so far amount to the id coercion?"
  
  ;; Precondition: d-id? <-> d == id

  ;; Postcondition: ret-id? -> ret == id

  (define-values (ret ret-id?)
    (let cc ([c c] [d d] [d-id? (eq? d 'id)] [e (hash)])
      (define p (cons c d))
      (define ref? (hash-ref e p #f))
      (match ref?
        [(μ _)
         (set-μ-ref! ref? #t)
         (values ref? #t)]
        [(box _)
         (unless (unbox ref?)
           (set-box! ref? (gensym)))
         (values (unbox ref?) #t)]
        [_
         (match* (c d)
           [(`(Seq ,g (! ,t0)) `(Seq (? ,t1) ,i))
            (define i0 (mc t0 t1))
            (define-values (c0 c0-id?) (cc i0 i (eq? i 'id) e))
            ;; Need to reason through all the T => G => T compositions
            ;; to figure out if adding the simple rule
            ;; (cc id id) => id
            ;; is the same as maintaining d-id? through
            (define-values (c1 c1-id?) (cc g c0 c0-id? e))
            (values c1 c1-id?)]
           [(`(Seq (? ,t1) ,i) d) 
            (define-values (c1 _) (cc i d d-id? e))
            (values `(Seq (? ,t1) ,c1) #f)]
           ;; The next case 'g' has to come after this case
           ;; to rule out it actually being a 'c'
           [(g `fail)
            (values `fail #f)]
           [(g0 `(Seq ,g1 (! ,t0)))
            (define-values (c1 _) (cc g0 g1 `(eq? g1 'id) e))
            (values `(Seq ,c1 (! ,t0)) #f)]
           [(`fail c)
            (values `fail #f)]
           [(`id d)
            ;; The d-id? has been maintained so that if this
            ;; case is reached we already know if d can be id?
            (values d d-id?)]
           [(`(,c0 -> ,c1) `(,d0 -> ,d1))
            (define-values (c2 i1) (cc d0 c0 (eq? c0 'id) e))
            (define-values (c3 i2) (cc c1 d1 (eq? d1 'id) e))
            (match* (c2 c3)
              [('id 'id) (values 'id #t)]
              [(c2 c3) (values `(,c2 -> ,c3) (and i1 i2))])]
           [(`#(,c0 ,c1) `#(,d0 ,d1))
            (define-values (c2 i1) (cc c0 d0 (eq? d0 'id) e))
            (define-values (c3 i2) (cc c1 d1 (eq? d1 'id) e))
            (match* (c2 c3)
              [('id 'id) (values 'id #t)]
              [(c2 c3) (values `#(,c2 ,c3) (and i1 i2))])]
           [(`(μ ,x ,_) d)
            (define used? (box #f))
            (define e0 (hash-set e p used?))
            (define c0 (unfold c))
            (define-values (c1 id?) (cc c0 d d-id? e0))
            (define used-sym? (unbox used?))
            (cond
              [id? (values 'id #t)]
              [used-sym? (values `(μ ,used-sym? ,c1) #f)]
              [else (values c1 #f)])]
           [(c `(μ ,y ,_))
            (define used? (box #f))
            (define e0 (hash-set e p used?))
            (define d0 (unfold d))
            ;; if d-id? then d had computational content and
            ;; therefore d0 has computational content
            (define-values (d1 id?) (cc c d0 d-id? e0))
            (define used-sym? (unbox used?))
            (cond
              [id? (values 'id #t)]
              [used-sym? (values `(μ ,used-sym? ,d1) #f)]
              [else (values d1 #f)])]
           [((μ c0) d)
            (define var/mu (μ #f))
            (define e0 (hash-set e p var/mu))
            (define-values (c1 id?) (cc c0 d d-id? e0))
            (define used? (μ-ref var/mu))
            (cond
              [id? (values 'id #t)]
              [used?
               (set-μ-ref! var/mu c1)
               (values var/mu #f)]
              [else (values c1 #f)])]
           [(c (μ d0))
            (define var/mu (μ #f))
            (define e0 (hash-set e p var/mu))
            (define-values (d1 id?) (cc c d0 #f e0))
            (define used? (μ-ref var/mu))
            (cond
              [id? (values 'id #t)]
              [used?
               (set-μ-ref! var/mu d1)
               (values var/mu #f)]
              [else (values d1 #f)])]
           [(_ _) (values 'fail #f)])])))
  ret)

(module+ test
  (test-pred "compose sanity"
             (check-α=? 'id)
             (compose-coercions 'id 'id))
  (test-pred "compose sanity"
             (check-α=? 'id)
             (compose-coercions '(Seq id (! Nat)) '(Seq (? Nat) id)))

  (test-pred "compose bigger 2"
             (check-α=? #((Seq (? Int) id) id))
             (compose-coercions '#(id (μ x #((Seq id (! Int)) x))) 
                                '(μ x #((Seq (? Int) id) x))))
  #;
  (test-pred "compose bigger"
             (check-α=? #((Seq (? Nat) id) (μ x #((Seq (? Nat) id) x))))
             (compose-coercions #(id (μ x #((Seq (? Nat) (Seq id (! Nat))) x)))
                                '(μ x #((Seq (? Int) id) x))))
  
  (test-pred "compose bigger 1"
             (check-α=? 'id)
             (compose-coercions '(μ x #((Seq id (! Int)) x))
                                '(μ x #((Seq (? Int) id) x)))))




(module+ test
  (define type-identity values)
  (define cast->crcn  (cast->coercion type-identity))
  (define cast->ecrcn (cast->coercion type->cyclic-type))
  (define evaluate/crcn
    (evaluate type-check cast->crcn (eval (unexpected 'cast) apply-coercion)))
  (define evaluate/ecrcn
    (evaluate type-check cast->ecrcn (eval (unexpected 'cast) apply-coercion)))
  (test-not-exn "eval p3 crcn" (thunk (evaluate/crcn p3)))
  (test-not-exn "eval p3 ecrcn" (thunk (evaluate/ecrcn p3)))


  ;; Build a value that we never use
  (define f (lambda (a) (error 'undefined)))

  (define c1
    (make-coercion (-μ x `(() -> #(Int ,x)))
                   (-μ y `(() -> #(?   ,y)))))

  (define g (apply-coercion f c1)) 

  (define c2 
    (make-coercion (-μ y `(() -> #(?   ,y)))
                   (-μ x `(()  -> #(Int ,x)))))
  
  (define h (apply-coercion g c2))

  (define c3
    (make-coercion (-μ y `(() -> #(?   ,y)))
                   (-μ x `(?  -> #(Int ,x)))))

  (define h0 (apply-coercion g c3))

  (evaluate/ecast
   '((define ones : (μ S2 (() -> #(Nat S2)))
       (λ (_ : ()) : (μ S #(Nat (() -> S)))
          #(1 ones)))
     (define dones : (μ S2 (() -> #(? S2)))
       ones)
     (define stream-ref : ((μ S2 (() -> #(? S2))) -> (Nat -> ?))
       (λ (s : (μ S2 (() -> #(? S2))))
         : (Nat -> ?)
         (λ (x : Nat) : ?
             (if (= x 0)
                 ((s ()) . 0)
                 ((stream-ref ((s ()) . 1))
                  (- x 1))))))
     (+ ((stream-ref dones) 100) 41)))

  (evaluate/ecast
   '((define from : (Nat -> (μ S2 (() -> #(Nat S2)))) 
       (λ (n : Nat)
         (λ (_ : ())
           #(n (from (+ n 1))))))
     (define base : (μ S2 (() -> #(? S2)))
       (from 2))
     (define cleanly-divisible? : (Nat -> (Nat -> Bool))
       (λ (n : Nat)
         (λ (m : Nat) 
           (= (% n m) 0))))
     (define filter : (Nat -> ((μ S2 (() -> #(? S2))) -> (μ S2 (() -> #(? S2)))))
       (λ (n : Nat)
         (λ (s : (μ S2 (() -> #(? S2))))
           (λ (_ : ()) 
             (let ([x (s ())])
               (if ((cleanly-divisible? (x . 0)) n)
                   ((x . 1) ())
                   #((x . 0) ((filter n) (x . 1)))))))))
     
     (define prime-sieve : ((μ S2 (() -> #(? S2))) -> (μ S2 (() -> #(? S2))))
       (λ (s : (μ S2 (() -> #(? S2))))
         (λ (_ : ())
           (let ([x (s ())])
             #((x . 0) (prime-sieve ((filter (x . 0)) (x . 1))))))))

     (define primes : (μ S2 (() -> #(? S2)))
       (prime-sieve (from 2)))

     (define stream-ref : ((μ S2 (() -> #(? S2))) -> (Nat -> ?))
       (λ (s : (μ S2 (() -> #(? S2))))
         (λ (x : Nat)
           (if (= x 0)
               ((s ()) . 0)
               ((stream-ref ((s ()) . 1)) (- x 1))))))

     (ann ((stream-ref primes) 100) Nat))))



;; Local Variables:
;; eval: (put (quote match\?) (quote racket-indent-function) 1)
;; eval: (activate-input-method "TeX")
;; End:

