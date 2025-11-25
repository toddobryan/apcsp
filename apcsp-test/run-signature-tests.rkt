#lang racket/base

(require rackunit/gui)
(require "./signature.rkt")

((make-gui-runner) all-signature-tests)