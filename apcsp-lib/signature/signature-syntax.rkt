#lang racket/base

(provide :
         signature signature/arbitrary
         define/signature define-values/signature
         -> mixed enum predicate combined property list-of nonempty-list-of)

(require "./signature.rkt"
         "./signature-unit.rkt"
         racket/promise
         (for-syntax racket/base)
         (for-syntax syntax/stx)
         (for-syntax stepper/private/syntax-property))

(define-for-syntax (phase-lift stx)
  (with-syntax [(:stx stx)]
    (with-syntax [(stx1 (syntax/loc stx #':stx))] ; attach the occurrence position to the syntax object
      #'stx1)))

(define-for-syntax (parse-signature name stx)
  (syntax-case* stx
    (mixed enum predicate list -> combined property reference at signature list-of nonempty-list-of)
    module-or-top-identifier=?
    [(mixed ?signature ...)
     (with-syntax ([?stx (phase-lift stx)]
                   [?name name]
                   [(?signature-expr ...) (map (lambda (sig)
                                                 (parse-signature #f sig))
                                               (syntax->list #'(?signature ...)))])
       #'(make-mixed-signature '?name
                               (list ?signature-expr ...)
                               ?stx))]
    [(enum ?exp ...)
     (with-syntax ((((?temp ?exp) ...)
                    (map list
                         (generate-temporaries #'(?exp ...)) (syntax->list #'(?exp ...))))
                   (?stx (phase-lift stx))
                   (?name name))
       (with-syntax (((?check ...)
                      (map (lambda (lis)
                             (with-syntax (((?temp ?exp) lis))
                               (with-syntax ((?raise
                                              (syntax/loc
                                                  #'?exp
                                                (error 'signatures "hier keine Signatur zulässig, nur normaler Wert"))))
                                 #'(when (signature? ?temp)
                                     ?raise))))
                           (syntax->list #'((?temp ?exp) ...)))))
         #'(let ((?temp ?exp) ...)
             ?check ...
             (make-case-signature '?name (list ?temp ...) equal? ?stx))))]
    [(predicate ?exp)
     (with-syntax ((?stx (phase-lift stx))
                   (?name name))
       #'(make-predicate-signature '?name (delay ?exp) ?stx))]
    [(list ?signature)
     (with-syntax ((?stx (phase-lift stx))
                   (?name name)
                   (?signature-expr (parse-signature #f #'?signature)))
       #'(make-list-signature '?name ?signature-expr ?stx))]
    [(list ?signature1 ?rest ...)
     (raise-syntax-error #f
                         "a list signature can only have one argument"
                         (syntax ?signature1))]
    [(list-of ?signature)
     (with-syntax ((?stx (phase-lift stx))
                   (?name name)
                   (?signature-expr (parse-signature #f #'?signature)))
       #'(make-list-signature '?name ?signature-expr ?stx))]
    [(list-of ?signature ...)
     (raise-syntax-error #f
                         "a list-of signature can only have one argument"
                         (syntax ?signature1))]
    [(nonempty-list-of ?signature)
     (with-syntax [(?stx (phase-lift stx))
                   (?name name)
                   (?signature-expr (parse-signature #f #'?signature))]
       #'(make-nonempty-list-signature '?name ?signature-expr ?stx))]
    [(nonempty-list-of ?signature ...)
     (raise-syntax-error #f
                         "a nonempty-list-of can only have one argument"
                         (syntax ?signature1))]
    [(?arg-signature ... -> ?return-signature)
     (with-syntax [(?stx (phase-lift stx))
                   (?name name)
                   [(?arg-signature-exprs ...) (map (lambda (sig)
                                                      (parse-signature #f sig))
                                                    (syntax->list #'(?arg-signature ...)))]
                   (?return-signature-expr (parse-signature #f #'?return-signature))]
       #'(make-procedure-signature '?name (list ?arg-signature-exprs ...) ?return-signature-expr ?stx))]
    [(?arg-signature ... -> ?return-signature1 ?return-signature2 . ?_)
     (raise-syntax-error #f
                         "only one signature is allowed after the ->"
                         (syntax ?return-signature2))]
    [(at ?loc ?sig)
     (with-syntax [(?sig-expr (parse-signature #f #'?sig))]
       #'(signature-update-syntax ?sig-expr #'?loc))]
    [signature
     (with-syntax [(?stx (phase-lift stx))]
       #'(signature-update-syntax signature/signature #'?loc))]
    [?id
     (identifier? #'?id)
     (with-syntax [(?stx (phase-lift stx))
                   (?name (or name (syntax->datum #'?id)))]
       (let [(name (symbol->string (syntax->datum #'?id)))]
         (if (char=? #\% (string-ref name 0))
             #'(make-type-variable-signature '?name ?stx)
             (with-syntax
                 [(?raise
                   (syntax/loc #'?stx
                     (error 'signatures "expected a signature, found ~e" ?id)))]
               (with-syntax
                   [(?sig
                     #'(make-delayed-signature '?name
                                               (delay
                                                 (begin
                                                   (when (not (signature? ?id))
                                                     ?raise)
                                                   ?id))))]
                 ;; for local variables (parameters, most probably),
                 ;; we want the value to determine the blame location
                 (if (eq? (identifier-binding #'?id) 'lexical)
                     #'?sig
                     #'(signature-update-syntax ?sig #'?stx)))))))]
    [(combined ?signature ...)
     (with-syntax [(?stx (phase-lift stx))
                   (?name name)
                   ((?signature-expr ...) (map (lambda (sig)
                                                 (parse-signature #f sig))
                                               (syntax->list #'(?signature ...))))]
       #'(make-combined-signature '?name
                                  (list ?signature-expr ...)
                                  ?stx))]
    [(property ?access ?signature)
     (with-syntax [(?stx (phase-lift stx))
                   (?name name)
                   (?signature-expr (parse-signature #f #'?signature))]
       #'(make-property-signature '?name
                                  ?access
                                  ?signature-expr
                                  ?stx))]
    ((signature ?stuff ...)
     (raise-syntax-error #f
                         "using signature as an operator not allowed"
                         stx))
    [(?signature-abstr ?signature ...)
     (and (identifier? #'?signature-abstr)
          ;; primarily worried about lambda
          (not (syntax-local-value #'?signature-abstr (lambda () #f))))
     (with-syntax [(?stx (phase-lift stx))
                   (?name name)
                   ((?signature-expr ...) (map (lambda (sig)
                                                 (let ((d (syntax->datum sig)))
                                                   ;; allow literals to be used directly
                                                   (if (or (number? d)
                                                           (boolean? d)
                                                           (string? d))
                                                       d
                                                       (parse-signature #f sig))))
                                               (syntax->list #'(?signature ...))))]
       
       (with-syntax
           [(?call (syntax/loc stx (?signature-abstr ?signature-expr ...)))]
         #'(make-call-signature '?name
                                (delay ?call)
                                (delay ?signature-abstr) (delay (list ?signature-expr ...))
                                ?stx)))]
    [else
     (raise-syntax-error #f
                         "invalid signature" stx)]))

(define signature/signature
  (make-predicate-signature 'signature
                            (delay signature?)
                            #f))

(define-syntax signature
  (lambda (stx)
    (syntax-case stx ()
      [(_ ?sig) #'(signature #f ?sig)]
      [(_ ?name ?sig) (stepper-syntax-property (parse-signature (syntax->datum #'?name) #'?sig)
                                               'stepper-skip-completely #t)])))

(define-syntax signature/arbitrary
  (λ (stx)
    (syntax-case stx ()
      [(_ ?arb ?sig . ?rest)
       #'(let [(sig (signature ?sig . ?rest))]
           (set-signature-arbitrary! sig ?arb)
           sig)])))

(define-syntax define/signature
  (λ (stx)
    (syntax-case stx ()
      [(_ ?name ?cnt ?expr)
       (with-syntax
           ([?enforced (stepper-syntax-property #'(attach-name '?name (apply/signature/blame ?cnt ?expr))
                                                'stepper-skipto/discard
                                                ;; apply-signature/blame takes care of itself
                                                ;; remember there's an implicit #%app
                                                '(syntax-e cdr syntax-e cdr cdr car))])
         #'(define ?name ?enforced))])))

(define-syntax define-values/signature
  (λ (stx)
    (syntax-case stx ()
      [(_ (?id ...) ?expr) (andmap identifier? (syntax->list #'(?id ...)))
                           (syntax-track-origin
                            #'(define-values (?id ...) ?expr)
                            stx
                            (car (syntax-e stx)))]
      [(_ ((?id ?cnt)) ?expr)
       (identifier? #'?id)
       #'(define/signature ?id ?cnt ?expr)] ; works with stepper
      [(_ (?bind ...) ?expr)
       (let ([ids+enforced (map (λ (bind)
                                  (syntax-case bind ()
                                    [?id (identifier? #'?id)
                                         (cons #'?id #'?id)]
                                    [(?id ?cnt) (identifier? #'?id)
                                                (cons #'?id
                                                      #'(attach-name '?id (apply-signature/blame ?cnt ?id)))]))
                                (syntax->list #'(?bind ...)))])
         (with-syntax ([(?id ...) (map car ids+enforced)]
                       [(?enforced ...) (map cdr ids+enforced)])
           (stepper-syntax-property
            #'(define-values (?id ...)
                (call-with-values
                 (lambda () ?expr)
                 (lambda (?id ...)
                   (values ?enforced ...))))
            'stepper-skip-completely #t)))])))

;; Matthew has promised a better way of doing this in the future.
(define (attach-name name thing)
  (if (and (procedure? thing)
           (not (signature? thing))) ; kludge: signatures are also procedures that output an error message
      (procedure-rename thing name)
      thing))

(define-syntax :
  (syntax-rules ()
    ((: ?id ?sig) (begin)))) ; probably never used, we're only interested in the binding for :

(define-for-syntax (outside-signature-syntax-error stx name)
  (raise-syntax-error #f
		      "only allowed in signatures"
		      name))

;; Expression -> Expression
;; Transforms unfinished code (... and the like) to code
;; raising an appropriate error.
(define-for-syntax outside-signature-syntax-transformer
  (make-set!-transformer
   (lambda (stx)
     (syntax-case stx (set!)
       [(set! form expr) (outside-signature-syntax-error stx (syntax form))]
       [(form . rest) (outside-signature-syntax-error stx (syntax form))]
       [form (outside-signature-syntax-error stx stx)]))))

(define-syntax -> outside-signature-syntax-transformer)
(define-syntax mixed outside-signature-syntax-transformer)
(define-syntax one-of outside-signature-syntax-transformer)
(define-syntax enum outside-signature-syntax-transformer)
(define-syntax predicate outside-signature-syntax-transformer)
(define-syntax combined outside-signature-syntax-transformer)
(define-syntax property outside-signature-syntax-transformer)
(define-syntax list-of outside-signature-syntax-transformer)
(define-syntax nonempty-list-of outside-signature-syntax-transformer)
