#lang racket/base

(provide (for-syntax binding-in-this-module?))

(require (for-syntax racket))

(define-for-syntax (binding-in-this-module? b)
  (and (list? b)
       (module-path-index? (car b))
       (let-values (((path base) (module-path-index-split (car b))))
	 (and (not path) (not base)))))