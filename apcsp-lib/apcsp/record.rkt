#lang racket

(provide define-record)

(require "private/primitives.rkt")

(require (for-syntax "private/syntax-checkers.rkt"))

(define-for-syntax (check-id-unbound! id)
  (cond
    [(identifier-binding id)
     => (lambda (binding)
          (if (binding-in-this-module? binding)
              (raise-syntax-error #f "the identifier is already defined" id)
              (raise-syntax-error #f "the identifier is already used by a built-in function" id)))]))

(define-syntax (define-record x)
  (syntax-case x ()
    [(_ type-spec constructor) #'(define-record type-spec constructor dummy-predicate)]
    [(_ type-spec constructor (accessor signature) field-spec ...)
     #'(define-record type-spec constructor dummy-predicate (accessor signature) field-spec ...)]
    [(_ type-spec constructor predicate field-spec ...)
     (with-syntax (((type-name type-params ...)
                    (if (identifier? #'type-spec)
                        #'(type-spec)
                        #'type-spec)))
       
       (check-for-id! (syntax type-name) "type is not identifier")
       
       (for-each
        (λ (type-param)
          (check-for-id! type-param "parameter to type constructor is not identifier"))
        (syntax->list #'(type-params ...)))
       
       (check-for-id! (syntax constructor) "constructor is not identifier")
       
       (check-for-id! (syntax predicate) "predicate is not identifier")
       
       (check-id-unbound! #'type-name)
       (check-id-unbound! #'constructor)
       (check-id-unbound! #'predicate)
       
       (for-each
        (λ (field-spec)
          (syntax-case field-spec ()
            [(accessor _)
             (begin
               (check-for-id! #'accessor "selector is not identifier")
               (check-id-unbound! #'accessor))]
            [stuff (raise-syntax-error #f "field does not have the form (selector signature)" #'stuff)]))
        (syntax->list #'(field-spec ...)))
       
       (with-syntax [(stx x)]
         #'(define-record* stx type-spec constructor predicate field-spec ...)))]))
    

