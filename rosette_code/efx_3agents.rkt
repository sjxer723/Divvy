#lang rosette

(require "defs/basic_model.rkt")
(require "defs/fairness.rkt")

(define n 3)
(define m 10)

(define (v0 a-val-matrix a-set) (valuation a-val-matrix 0 a-set m))
(define (v1 a-val-matrix a-set) (valuation a-val-matrix 1 a-set m))
(define (v2 a-val-matrix a-set) (valuation a-val-matrix 2 a-set m))

;;; "I cut you choose" for EFX with three agents
(define (i-cut-u-choose-for-efx-three-agent a-val-matrix an-alloc n m)
    (if (and 
            (<= (v1 a-val-matrix (list-ref an-alloc 0)) (v1 a-val-matrix (list-ref an-alloc 1)))
            (<= (v1 a-val-matrix (list-ref an-alloc 2)) (v1 a-val-matrix (list-ref an-alloc 1)))
        )   ; agent 2 favors (bundle 1)
        (if (<= (v2 a-val-matrix (list-ref an-alloc 0)) (v2 a-val-matrix (list-ref an-alloc 2)))
            an-alloc ; agent 3 favors (bundle 2)
            (swap-bundle an-alloc 0 2 n) ; agent 3 favors (bundle 0)
        )
        (
            if (and 
                (<= (v1 a-val-matrix (list-ref an-alloc 1)) (v1 a-val-matrix (list-ref an-alloc 0)))
                (<= (v1 a-val-matrix (list-ref an-alloc 2)) (v1 a-val-matrix (list-ref an-alloc 0)))
            ) ; agent 2 favors (bundle 0)
            (if (<= (valuation a-val-matrix 2 (list-ref an-alloc 1) m) (v2 a-val-matrix (list-ref an-alloc 2)))
                (swap-bundle an-alloc 0 1 n) ; agent 3 favors (bundle 2)
                (swap-bundle (swap-bundle an-alloc 1 2 n) 0 1 n) ; agent 3 favors (bundle 1)
            )
            ; agent 2 favors (bundle 3)
            (if (<= (v2 a-val-matrix (list-ref an-alloc 0)) (v2 a-val-matrix (list-ref an-alloc 1)))
                (swap-bundle an-alloc 1 2 n) ; agent 3 favors (bundle 1)
                (swap-bundle (swap-bundle an-alloc 0 2 n) 0 1 n) ; agent 3 favors (bundle 0)
            )
        )
    )
)

(define init-alloc (alloc n m))
(define M1 (create-valuations n m))
(assert (feasible-alloc? init-alloc n m))
(assert (nonegative-value? M1 n m))
(assert (identical-EFX-alloc-for-agent-i? M1 0 init-alloc n m))
(assert (not (EFX-alloc? M1 (i-cut-u-choose-for-efx-three-agent M1 init-alloc n m) n m)))

(evaluate M1 (solve #t))
(evaluate init-alloc (solve #t))
; evaluate fairness criteria
(evaluate (EF1-alloc-for-agent-i? M1 0 (i-cut-u-choose-for-efx-three-agent M1 init-alloc n m) n m) (solve #t))
(evaluate (EF1-alloc-for-agent-i? M1 1 (i-cut-u-choose-for-efx-three-agent M1 init-alloc n m) n m) (solve #t))
(evaluate (EF1-alloc-for-agent-i? M1 2 (i-cut-u-choose-for-efx-three-agent M1 init-alloc n m) n m) (solve #t))