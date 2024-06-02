#lang rosette

(require "defs/permutation.rkt")
(require "defs/basic_model.rkt")
(require "defs/fairness.rkt")

(define n 2)
(define m 4)

(define even-cut-alloc
    (for/list ([i (in-range n)])
        (for/list ([j (in-range m)])
            (if (even? i) 
                (if (even? j) #t #f) 
                (if (even? j) #f #t))
        )
    ))

(define (even-cut-alloc-as-perm a-perm)
    (for/list ([i (in-range n)])
        (for/list ([j (in-range m)])
            (if (even? i) 
                (if (even? (list-ref a-perm j)) #t #f) 
                (if (even? (list-ref a-perm j)) #f #t))
        )
    ))

(define (i-cut-u-choose a-val-matrix an-alloc)
    (if (<= (valuation a-val-matrix 1 (list-ref an-alloc 0) m) 
            (valuation a-val-matrix 1 (list-ref an-alloc 1) m))
        an-alloc
        (swap-bundle an-alloc 0 1)
    )
)

(define M1 (create-valuations n m))
(define M2 (create-valuations n m))
(define sigma (permutation m))
(define M3 (list-set M1 0 (list-ref M2 0)))
(assert (valid-permutation? sigma m))

(assert (nonegative-value? M1 n m))
(assert (nonegative-value? M3 n m))

(assert (nondecreasing-value-by-index? M1 0 m))
(assert (nondecreasing-value-by-perm? M3 sigma 0 m))

(assert (feasible-alloc? even-cut-alloc n m))
(assert (feasible-alloc? (even-cut-alloc-as-perm sigma) n m))

(define final-alloc1 (i-cut-u-choose M1 even-cut-alloc))
(define final-alloc2 (i-cut-u-choose M3 (even-cut-alloc-as-perm sigma)))

(assert (EF1-alloc? M1 final-alloc1 n m))
(assert (EF1-alloc? M3 final-alloc2 n m))

; Misreporting gets higher value
(assert (<  (valuation M1 0 (list-ref final-alloc1 0) m)
            (valuation M1 0 (list-ref final-alloc2 0) m)))

(evaluate M1 (solve #t))
(evaluate M3 (solve #t))
(evaluate sigma (solve #t))

(evaluate (even-cut-alloc-as-perm sigma) (solve #t))
(evaluate (i-cut-u-choose M3 (even-cut-alloc-as-perm sigma)) (solve #t))
(evaluate final-alloc1 (solve #t))
(evaluate final-alloc2 (solve #t))
