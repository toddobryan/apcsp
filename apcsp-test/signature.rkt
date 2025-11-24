#lang racket/base

(provide all-signature-tests)

(require rackunit
         racket/promise
         "../apcsp-lib/apcsp/record.rkt"
         "../apcsp-lib/signature/signature.rkt"
         "../apcsp-lib/signature/signature-syntax.rkt"
         "../apcsp-lib/signature/signature-unit.rkt")

(define Int (make-predicate-signature 'Int integer? 'Int-marker))
(define Boolean (make-predicate-signature 'Boolean boolean? 'Boolean-marker))
(define %a (make-type-variable-signature 'a 'a-marker))
(define %b (make-type-variable-signature 'b 'b-marker))

(define-syntax say-no
  (syntax-rules ()
    [(say-no ?body ...)
     (let/ec exit
       (call-with-signature-violation-proc
        (lambda (obj signature message blame)
          (exit 'no))
        (lambda ()
          ?body ...)))]))

(define-syntax failed-signature
  (syntax-rules ()
    [(say-no ?body ...)
     (let/ec exit
       (call-with-signature-violation-proc
        (lambda (obj signature message blame)
          (exit signature))
        (lambda ()
          ?body ...)))]))

(define signature-tests
  (test-suite
   "Tests for signature combinators"
   
   (test-case
    "flat"
    (check-equal? (say-no (apply-signature Int 5)) 5)
    (check-equal? (say-no (apply-signature Int "foo")) 'no))
   
   (test-case
    "list"
    (check-equal? (say-no (apply-signature (signature x (list-of %a)) 5)) 'no)
    (check-equal? (say-no (apply-signature (signature x (list-of %a)) '(1 2 3))) '(1 2 3))
    (check-equal? (say-no (apply-signature (signature x (list-of (predicate integer?))) '(1 2 3))) '(1 2 3))
    (check-equal? (say-no (apply-signature (signature x (list-of (predicate integer?))) '(1 #f 3))) 'no))

   (test-case
    "mixed"
    (define Int-or-Bool (signature (mixed Int Boolean)))
    (check-equal? (say-no (apply-signature Int-or-Bool #f))
		  #f)
    (check-equal? (say-no (apply-signature Int-or-Bool 17))
		  17)
    (check-equal? (say-no (apply-signature Int-or-Bool "foo"))
		  'no))

   (test-case
    "combined"
    (define Octet (signature (combined Int
                                       (predicate (lambda (x)
                                                    (< x 256)))
                                       (predicate (lambda (x)
                                                    (>= x 0))))))
    (check-equal? (say-no (apply-signature Octet #f))
		  'no)
    (check-equal? (say-no (apply-signature Octet 17))
		  17)
    (check-equal? (say-no (apply-signature Octet 0))
		  0)
    (check-equal? (say-no (apply-signature Octet -1))
		  'no)
    (check-equal? (say-no (apply-signature Octet 255))
		  255)
    (check-equal? (say-no (apply-signature Octet 256))
		  'no)
    (check-equal? (say-no (apply-signature Octet "foo"))
		  'no))  
   ))

(define all-signature-tests
  (test-suite "all-signature-tests"
              signature-tests))
              ;signature-syntax-tests))