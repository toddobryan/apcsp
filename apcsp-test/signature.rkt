#lang racket/base

(provide all-signature-tests)

(require rackunit
         rackunit/text-ui
         racket/promise
         "../apcsp-lib/apcsp/record.rkt"
         "../apcsp-lib/signature/signature.rkt"
         "../apcsp-lib/signature/signature-unit.rkt"
         (rename-in "../apcsp-lib/signature/signature-syntax.rkt"
                    [list-of List]
                    [nonempty-list-of Nel]
                    [mixed Or]
                    [combined And]))

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
    "nonempty list"
    (define Int-list (make-nonempty-list-signature 'Int-list Int #f))
    (check-equal? (say-no (apply-signature Int-list '(1 2 3)))
                  '(1 2 3))
    (check-equal? (say-no (apply-signature Int-list '#f))
                  'no)
    (check-equal? (say-no (apply-signature Int-list '()))
                  'no)
    (check-eq? (failed-signature (apply-signature Int-list '(1 #f 3)))
               Int))

   (test-case
    "list-cached"
    (define Int-list (make-list-signature 'Int-list Int #f))
    (define Boolean-list (make-list-signature 'Boolean-list Boolean #f))
    (define l '(1 2 3))
    (define foo "foo")
    (define no '(1 #f 3))
    (define no2 '(1 #f 3))
    (define Int-list->Boolean (make-procedure-signature 'Int-list->Boolean (list Int-list) Boolean 'Int->Boolean-marker))

    (check-equal? (say-no (apply-signature Int-list l))
                  '(1 2 3))
    (check-equal? (say-no (apply-signature Int-list l))
                  '(1 2 3))
    (check-equal? (say-no (apply-signature Boolean-list l))
                  'no)
    (check-equal? (say-no (apply-signature Int-list foo))
                  'no)
    (check-equal? (say-no (apply-signature Int-list foo))
                  'no)
    (check-eq? (failed-signature (apply-signature Int-list no))
               Int)
    (check-eq? (failed-signature (apply-signature Int-list no))
               Int)

    (let ((proc (say-no (apply-signature Int-list->Boolean (lambda (l) (even? (car l)))))))
      (check-equal? (say-no (proc no)) 'no)
      (check-equal? (say-no (proc no)) 'no)
      (check-equal? (say-no (proc no2)) 'no)
      (check-equal? (say-no (proc no2)) 'no))
    )

   (test-case
    "vector"
    (define Int-vector (make-vector-signature 'Int-vector Int #f))
    (define Vector (make-vector-signature 'Vector %a #f))
    (check-equal? (say-no (apply-signature Int-vector '#(1 2 3)))
                  '#(1 2 3))
    (check-equal? (say-no (apply-signature Vector '#(1 2 3)))
                  '#(1 2 3))
    (check-equal? (say-no (apply-signature Int-vector '#f))
                  'no)
    (check-eq? (failed-signature (apply-signature Int-vector '#(1 #f 3)))
               Int))

   (test-case
    "vector/cached"
    (let [(count 0)]
      (define counting-integer
        (make-predicate-signature 'counting-integer
                                  (lambda (obj)
                                    (set! count (+ 1 count))
                                    (integer? obj))
                                  'Int-marker))

      (define Int-vector (make-vector-signature 'Int-list counting-integer #f))

      (define v1 '#(1 2 3))

      (check-eq? (say-no (apply-signature Int-vector v1))
                 v1)
      (check-equal? count 3)
      (check-eq? (say-no (apply-signature Int-vector v1))
                 v1)
      (check-equal? count 3)))

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

   (test-case
    "case"
    (define foo-or-bar (make-case-signature 'foo-or-bar '("foo" "bar") equal? 'foo-or-bar-marker))
    (check-equal? (say-no (apply-signature foo-or-bar #f))
                  'no)
    (check-equal? (say-no (apply-signature foo-or-bar "foo"))
                  "foo")
    (check-equal? (say-no (apply-signature foo-or-bar "bar"))
                  "bar"))

   (test-case
    "procedure"
    (define Int->Boolean (make-procedure-signature 'Int->Boolean (list Int) Boolean 'Int->Boolean-marker))
    (check-equal? (say-no (apply-signature Int->Boolean #f))
                  'no)
    (check-equal? (say-no (apply-signature Int->Boolean (lambda () "foo")))
                  'no)
    (check-equal? (say-no (apply-signature Int->Boolean (lambda (x y) "foo")))
                  'no)
    (let ((proc (say-no (apply-signature Int->Boolean (lambda (x) (odd? x))))))
      (check-pred procedure? proc)
      (check-equal? (proc 15) #t)
      (check-equal? (proc 16) #f)
      (check-equal? (say-no (proc "foo")) 'no))
    (let ((proc (say-no (apply-signature Int->Boolean (lambda (x) (+ x 1))))))
      (check-equal? (say-no (proc 12)) 'no)))

   (test-case
    "type variable - simple"
    (check-equal? (say-no (apply-signature %a #f)) #f)
    (check-equal? (say-no (apply-signature %a 15)) 15))

   (test-case
    "type variable - list"
    (define a-list (make-list-signature 'a-list %a #f))
    (check-equal? (say-no (apply-signature a-list '(1 2 3)))
                  '(1 2 3))
    (check-equal? (say-no (apply-signature a-list '#f))
                  'no)
    (check-equal? (say-no (apply-signature a-list '(#f "foo" 5)))
                  '(#f "foo" 5)))

   (test-case
    "apply-signature/blame"
    (define Int->Boolean (make-procedure-signature 'Int->Boolean (list Int) Boolean 'Int->Boolean-marker))
    (let ([proc (say-no (apply-signature/blame Int->Boolean (lambda (x) (odd? x))))])
      (check-pred procedure? proc)
      (check-equal? (proc 15) #t)
      (check-equal? (proc 16) #f)
      (check-equal? (say-no (proc "foo")) 'no))
    (let ([proc (say-no (apply-signature/blame Int->Boolean (lambda (x) x)))])
      (call-with-signature-violation-proc
       (lambda (obj signature message blame)
         (check-true (srcloc? blame)))
       (lambda ()
         (proc 5)))))
   ))

(define signature-syntax-tests
  (test-suite
   "Tests for signature syntax"

   (test-case
    "predicate"
    (define Int (signature (predicate integer?)))
    (check-equal? (say-no (apply-signature Int 5)) 5)
    (check-equal? (say-no (apply-signature Int "foo")) 'no))

   (test-case
    "list"
    (check-equal? (say-no (apply-signature (signature x (List %a)) 5)) 'no)
    (check-equal? (say-no (apply-signature (signature x (List %a)) '(1 2 3))) '(1 2 3))
    (check-equal? (say-no (apply-signature (signature x (List (predicate integer?))) '(1 2 3))) '(1 2 3))
    (check-equal? (say-no (apply-signature (signature x (List (predicate integer?))) '(1 #f 3))) 'no))

   (test-case
    "mixed"
    (define IntOrBool (signature (Or Int Boolean)))
    (check-equal? (say-no (apply-signature IntOrBool #f))
                  #f)
    (check-equal? (say-no (apply-signature IntOrBool 17))
                  17)
    (check-equal? (say-no (apply-signature IntOrBool "foo"))
                  'no))

   (test-case
    "combined"
    (define Octet (signature (And Int
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

   (test-case
    "procedure"
    (define Int->Boolean (signature Int->Boolean ((predicate integer?) -> (predicate boolean?))))
    (check-equal? (say-no (apply-signature Int->Boolean #f))
                  'no)
    (check-equal? (say-no (apply-signature Int->Boolean (lambda () "foo")))
                  'no)
    (check-equal? (say-no (apply-signature Int->Boolean (lambda (x y) "foo")))
                  'no)
    (let ((proc (say-no (apply-signature Int->Boolean (lambda (x) (odd? x))))))
      (check-pred procedure? proc)
      (check-equal? (proc 15) #t)
      (check-equal? (proc 16) #f)
      (check-equal? (say-no (proc "foo")) 'no))
    (let ((proc (say-no (apply-signature Int->Boolean (lambda (x) (+ x 1))))))
      (check-equal? (say-no (proc 12)) 'no)))


   (test-case
    "record-wrap"
    (define-record (pare-of a b) kons pare? (kar a) (kdr b))
    (define ctr (pare-of integer boolean))
    (let ((obj (apply-signature ctr (kons 1 #t))))
      (check-equal? (kar obj) 1)
      (check-equal? (kdr obj) #t))
    (check-equal? (say-no (apply-signature ctr (kons 1 2))) 'no)
    )

   (test-case
    "record-wrap/lazy"
    (define-struct pare (kar kdr extra)
      #:mutable
      #:property prop:lazy-wrap
      (make-lazy-wrap-info
       (lambda (kar kdr) (kons kar kdr))
       (list (lambda (x) (pare-kar x)) (lambda (x) (pare-kdr x)))
       (list (lambda (x v) (set-pare-kar! x v))
             (lambda (x v) (set-pare-kdr! x v)))
       (lambda (x) (pare-extra x)) (lambda (x v) (set-pare-extra! x v))))
    (define (kons kar kdr)
      (make-pare kar kdr #f))
    (define (kar p)
      (check-lazy-wraps! struct:pare p)
      (pare-kar p))
    (define (kdr p)
      (check-lazy-wraps! struct:pare p)
      (pare-kdr p))
    (define (pare-of kar-sig kdr-sig)
      (make-lazy-wrap-signature 'pare #f
                                struct:pare
                                pare?
                                (list kar-sig kdr-sig)
                                #f))
    (define ctr (pare-of integer boolean))
    (let ((obj (apply-signature ctr (kons 1 #t))))
      (check-equal? (kar obj) 1)
      (check-equal? (kdr obj) #t))
    (let ((obj (apply-signature ctr (kons 1 2))))
      (check-equal? (say-no (kar obj)) 'no))
    )

   (test-case
    "record-wrap-2"
    (let ((count 0))
      (define counting-integer
        (make-predicate-signature 'counting-integer
                                  (lambda (obj)
                                    (set! count (+ 1 count))
                                    (integer? obj))
                                  'integer-marker))
      (define-record (pare-of a b) kons pare? (kar a) (kdr b))
      (define ctr (signature (pare-of counting-integer boolean)))
      (let ((obj (apply-signature ctr (apply-signature ctr (kons 1 #t)))))
        (check-equal? count 1)
        (check-equal? (kar obj) 1)
        (check-equal? count 1)
        (check-equal? (kdr obj) #t)
        (check-equal? count 1))))

   (test-case
    "record-wrap-2/lazy"
    (let ((count 0))
      (define counting-integer
        (make-predicate-signature 'counting-integer
                                  (lambda (obj)
                                    (set! count (+ 1 count))
                                    (integer? obj))
                                  'integer-marker))

      (define-struct pare (kar kdr extra)
        #:mutable
        #:property prop:lazy-wrap
        (make-lazy-wrap-info
         (lambda (kar kdr) (kons kar kdr))
         (list (lambda (x) (pare-kar x)) (lambda (x) (pare-kdr x)))
         (list (lambda (x v) (set-pare-kar! x v))
               (lambda (x v) (set-pare-kdr! x v)))
         (lambda (x) (pare-extra x)) (lambda (x v) (set-pare-extra! x v))))
      (define (kons kar kdr)
        (make-pare kar kdr #f))
      (define (kar p)
        (check-lazy-wraps! struct:pare p)
        (pare-kar p))
      (define (kdr p)
        (check-lazy-wraps! struct:pare p)
        (pare-kdr p))
      (define (pare-of kar-sig kdr-sig)
        (make-lazy-wrap-signature 'pare #f
                                  struct:pare
                                  pare?
                                  (list kar-sig kdr-sig)
                                  #f))

      (define ctr (signature (pare-of counting-integer boolean)))
      (let ((obj (apply-signature ctr (apply-signature ctr (kons 1 #t)))))
        (check-equal? count 0)
        (check-equal? (kar obj) 1)
        (check-equal? count 1)
        (check-equal? (kdr obj) #t)
        (check-equal? count 1))))

   (test-case
    "record-wrap-3"
    (let ((count 0))
      (define counting-integer
        (make-predicate-signature 'counting-integer
                                  (lambda (obj)
                                    (set! count (+ 1 count))
                                    (integer? obj))
                                  'integer-marker))

      (define-record (pare-of a b) kons pare? (kar a) (kdr b))
      (define ctr (signature (pare-of counting-integer boolean)))
      (let ((obj (apply-signature ctr (apply-signature ctr (kons 1 #t)))))
        (check-equal? count 1)
        (check-equal? (kar obj) 1)
        (check-equal? count 1)
        (check-equal? (kdr obj) #t)
        (check-equal? count 1)
        ;; after checking, the system should remember that it did so
        (let ((obj-2 (apply-signature ctr obj)))
          (check-equal? count 1)
          (check-equal? (kar obj) 1)
          (check-equal? count 1)
          (check-equal? (kdr obj) #t)
          (check-equal? count 1)))))

   (test-case
    "record-wrap-3/lazy"
    (let ((count 0))
      (define counting-integer
        (make-predicate-signature 'counting-integer
                                  (lambda (obj)
                                    (set! count (+ 1 count))
                                    (integer? obj))
                                  'integer-marker))
      (define-struct pare (kar kdr extra)
        #:mutable
        #:property prop:lazy-wrap
        (make-lazy-wrap-info
         (lambda (kar kdr) (kons kar kdr))
         (list (lambda (x) (pare-kar x)) (lambda (x) (pare-kdr x)))
         (list (lambda (x v) (set-pare-kar! x v))
               (lambda (x v) (set-pare-kdr! x v)))
         (lambda (x) (pare-extra x)) (lambda (x v) (set-pare-extra! x v))))
      (define (kons kar kdr)
        (make-pare kar kdr #f))
      (define (kar p)
        (check-lazy-wraps! struct:pare p)
        (pare-kar p))
      (define (kdr p)
        (check-lazy-wraps! struct:pare p)
        (pare-kdr p))
      (define (pare-of kar-sig kdr-sig)
        (make-lazy-wrap-signature 'pare #f
                                  struct:pare
                                  pare?
                                  (list kar-sig kdr-sig)
                                  #f))

      (define ctr (signature (pare-of counting-integer boolean)))
      (let ((obj (apply-signature ctr (apply-signature ctr (kons 1 #t)))))
        (check-equal? count 0)
        (check-equal? (kar obj) 1)
        (check-equal? count 1)
        (check-equal? (kdr obj) #t)
        (check-equal? count 1)
        ;; after checking, the system should remember that it did so
        (let ((obj-2 (apply-signature ctr obj)))
          (check-equal? count 1)
          (check-equal? (kar obj) 1)
          (check-equal? count 1)
          (check-equal? (kdr obj) #t)
          (check-equal? count 1)))))

   (test-case
    "double-wrap"
    (let ((count 0))
      (define counting-integer
        (make-predicate-signature 'counting-integer
                                  (lambda (obj)
                                    (set! count (+ 1 count))
                                    (integer? obj))
                                  'integer-marker))
      (define-record (pare-of a b) raw-kons pare? (kar a) (kdr b))

      (define empty-list (signature (predicate null?)))

      (define my-list-of
        (lambda (x)
          (signature (mixed empty-list
                            (pare-of x (my-list-of x))))))

      (define/signature kons (signature (%a (my-list-of %a) -> (pare-of %a (my-list-of %a))))
        raw-kons)

      (define/signature build-list (signature (integer -> (my-list-of counting-integer)))
        (lambda (n)
          (if (= n 0)
              '()
              (kons n (build-list (- n 1))))))

      (define/signature list-length (signature ((my-list-of counting-integer) -> integer))
        (lambda (lis)
          (cond
            ((null? lis) 0)
            ((pare? lis)
             (+ 1 (list-length (kdr lis)))))))

      ;; one wrap each for (my-list-of %a), one for (my-list-of counting-integer)
      (let  ((l1 (build-list 10)))
        (check-equal? count 10)
        (let ((len1 (list-length l1)))
          (check-equal? count 10)))))

   (test-case
    "double-wrap/lazy"
    (let ((count 0))
      (define counting-integer
        (make-predicate-signature 'counting-integer
                                  (lambda (obj)
                                    (set! count (+ 1 count))
                                    (integer? obj))
                                  'integer-marker))

      (define-struct pare (kar kdr extra)
        #:mutable
        #:property prop:lazy-wrap
        (make-lazy-wrap-info
         (lambda (kar kdr) (raw-kons kar kdr))
         (list (lambda (x) (pare-kar x)) (lambda (x) (pare-kdr x)))
         (list (lambda (x v) (set-pare-kar! x v))
               (lambda (x v) (set-pare-kdr! x v)))
         (lambda (x) (pare-extra x)) (lambda (x v) (set-pare-extra! x v))))
      (define (raw-kons kar kdr)
        (make-pare kar kdr #f))
      (define (kar p)
        (check-lazy-wraps! struct:pare p)
        (pare-kar p))
      (define (kdr p)
        (check-lazy-wraps! struct:pare p)
        (pare-kdr p))
      (define (pare-of kar-sig kdr-sig)
        (make-lazy-wrap-signature 'pare #f
                                  struct:pare
                                  pare?
                                  (list kar-sig kdr-sig)
                                  #f))


      (define empty-list (signature (predicate null?)))

      (define my-list-of
        (lambda (x)
          (signature (mixed empty-list
                            (pare-of x (my-list-of x))))))

      (define/signature kons (signature (%a (my-list-of %a) -> (pare-of %a (my-list-of %a))))
        raw-kons)

      (define/signature build-list (signature (integer -> (my-list-of counting-integer)))
        (lambda (n)
          (if (= n 0)
              '()
              (kons n (build-list (- n 1))))))

      (define/signature list-length (signature ((my-list-of counting-integer) -> integer))
        (lambda (lis)
          (cond
            ((null? lis) 0)
            ((pare? lis)
             (+ 1 (list-length (kdr lis)))))))

      ;; one wrap each for (my-list-of %a), one for (my-list-of counting-integer)
      (let  ((l1 (build-list 10)))
        (check-equal? count 0)
        (let ((len1 (list-length l1)))
          (check-equal? count 10)))))

   (test-case
    "mixed wrap"

    (define-struct pare (kar kdr extra)
      #:mutable
      #:property prop:lazy-wrap
      (make-lazy-wrap-info
       (lambda (kar kdr) (raw-kons kar kdr))
       (list (lambda (x) (pare-kar x)) (lambda (x) (pare-kdr x)))
       (list (lambda (x v) (set-pare-kar! x v))
             (lambda (x v) (set-pare-kdr! x v)))
       (lambda (x) (pare-extra x)) (lambda (x v) (set-pare-extra! x v))))
    (define (raw-kons kar kdr)
      (make-pare kar kdr #f))
    (define (kar p)
      (check-lazy-wraps! struct:pare p)
      (pare-kar p))
    (define (kdr p)
      (check-lazy-wraps! struct:pare p)
      (pare-kdr p))
    (define (pare-of kar-sig kdr-sig)
      (make-lazy-wrap-signature 'pare #f
                                struct:pare
                                pare?
                                (list kar-sig kdr-sig)
                                #f))


    (define sig1 (signature (pare-of integer boolean)))
    (define sig2 (signature (pare-of boolean integer)))
    (define sig (signature (mixed sig1 sig2)))
    (define/signature x sig (raw-kons #t 15))
    (define/signature y sig (raw-kons #t #t))
    (check-equal? (kar x) #t)
    (check-equal? (say-no (kar y)) 'no))

   (test-case
    "wrap equality"
    (define-record (pare-of a b) raw-kons pare? (kar a) (kdr b))

    (define empty-list (signature (predicate null?)))

    (define my-list-of
      (lambda (x)
        (signature (mixed empty-list
                          (pare-of x (my-list-of x))))))

    (define/signature kons (signature (%a (my-list-of %a) -> (pare-of %a (my-list-of %a))))
      raw-kons)

    (check-equal? (raw-kons 1 '()) (raw-kons 1 '()))
    (check-equal? (kons 1 '()) (kons 1 '()))
    (check-equal? (kons 1 '()) (raw-kons 1 '()))
    (check-equal? (raw-kons 1 '()) (kons 1 '())))

   (test-case
    "pair-wrap"
    (define sig (make-pair-signature #f integer boolean))
    (let ((obj (apply-signature sig (cons 1 #t))))
      (check-equal? (checked-car obj) 1)
      (check-equal? (checked-cdr obj) #t))
    (let ((obj (apply-signature sig (cons 1 2))))
      (check-equal? (say-no (checked-car obj)) 'no))
    )
   ))


(define all-signature-tests
  (test-suite "all-signature-tests"
              signature-tests
              signature-syntax-tests))
