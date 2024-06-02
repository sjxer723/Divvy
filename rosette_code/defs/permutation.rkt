#lang rosette

(require "./basic_model.rkt")

(provide permutation)
(provide valid-permutation?)
(provide nondecreasing-value-by-index?)
(provide nondecreasing-value-by-perm?)


; n agents
;;; (define n 3)
; m items
;;; (define m 10)

(define (permutation len)
  (for/list ([i (range len)])
    (define-symbolic* loc integer?)
    (assert (and (>= loc 0) (< loc len)))
    loc))

;; check whether a permutation is valid
(define (valid-permutation? a-permutation len)
    ; distinct elements 
    (andmap
        (λ (i) 
            (andmap 
                (λ (j)
                (or (= i j) (not (= (list-ref a-permutation i) (list-ref a-permutation j)))))
            (range len))
        )
        (range len)  
    )
)

(define (nondecreasing-value-by-index? a-val-matrix i m)
    (andmap
        (λ (j)
            (andmap
                (λ (k) 
                    (or (> j k)
                        (<= (list-ref (list-ref a-val-matrix i) j) 
                            (list-ref (list-ref a-val-matrix i) k))
                    ))
                (range m)
            )
        )
    (range m))
)

;;; Given a permutation σ,
;;;     σ(j) < σ(k) -> v_i(σ(j)) < v_i(σ(k))
(define (nondecreasing-value-by-perm? a-val-matrix a-perm i m)
    (andmap
        (λ (j)
            (andmap
                (λ (k) 
                    (or 
                        (>= (list-ref a-perm j) (list-ref a-perm k))
                        (< (list-ref (list-ref a-val-matrix i) j)
                            (list-ref (list-ref a-val-matrix i) k))
                    )
                    )
                (range m)
            )
        )
    (range m))
)

;;; (define a-permutation (permutation 10))
;;; (assert (valid-permutation? a-permutation 10))
;;; (evaluate a-permutation (solve #t))
