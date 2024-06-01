#lang rosette

; n agents
(define n 3)
; m items
(define m 10)

(define (create-sym-list n)
    (for/list ([i (in-range n)])
        (define-symbolic* xi real?) xi))

(define valuations
    (for/list ([i (in-range n)]) 
            (create-sym-list m)))

;;; (printf "Symbolic list: ~a\n" valuations)

(define alloc
    (map (λ (i)
         (define-symbolic* x boolean?
           #:length m)
         x)
       (range n)))

(define (swap-bundle an-alloc i j) 
    (map (λ (k) 
            (if (= k i) (list-ref an-alloc j)
                    (if (= k j) (list-ref an-alloc i) (list-ref an-alloc k)))
        )
        (range n))
)

(define (count-trues l)
  (apply
   +
   (map
    (λ (b) (if b 1 0))
    l)))

(define (feasible-alloc? an-alloc)
  (andmap
   (λ (j)
     (= (count-trues (map (λ (i) (list-ref (list-ref alloc i) j)) (range n))) 1))
   (range m)))

(define (valuation i a-set)
  (apply + (for/list ([k (range m)])
             (if (list-ref a-set k)
                 (list-ref (list-ref valuations i) k) 0))))

(define (remove-from-set a-set j)
    (map (λ (i) (if (= i j) #f (list-ref a-set i))) (range (length a-set)))
)

;;; (printf "~a\n" (remove-from-set '(#f #t #f #f) 1))

(define (EF1-alloc-for-agent-i? i1 an-alloc)
    (andmap
      (λ (i2)
        (or
         (ormap
          (λ (j)
            (>= (valuation i1 (list-ref an-alloc i1))
                (valuation i1
                           (remove-from-set (list-ref an-alloc i2) j))))
          (range m))
         (>= (valuation i1 (list-ref an-alloc i1))
             (valuation i1 (list-ref an-alloc i2)))))
      (range n))
)

(define (identical-EF1-alloc-for-agent-i? i1 an-alloc)
    (andmap
      (λ (i2) (EF1-alloc-for-agent-i? i1 (swap-bundle an-alloc i1 i2)))
      (range n))
)

(define (EFX-alloc-for-agent-i? i1 an-alloc)
    (andmap
      (λ (i2)
        (or
         (andmap
          (λ (j)
            (>= (valuation i1 (list-ref an-alloc i1))
                (valuation i1
                           (remove-from-set (list-ref an-alloc i2) j))))
          (range m))
         (>= (valuation i1 (list-ref an-alloc i1))
             (valuation i1 (list-ref an-alloc i2)))))
      (range n))
)

(define (identical-EFX-alloc-for-agent-i? i1 an-alloc)
    (andmap
      (λ (i2) (EFX-alloc-for-agent-i? i1 (swap-bundle an-alloc i1 i2)))
      (range n))
)

(define (EF1-alloc? an-alloc)
  (andmap
   (λ (i1)
     (EF1-alloc-for-agent-i? i1 an-alloc))
   (range n)))

(define (EFX-alloc? an-alloc)
  (andmap
   (λ (i1)
     (EFX-alloc-for-agent-i? i1 an-alloc))
   (range n)))

(define (nonegative-value? valuations)
    (andmap
        (λ (i)
            (andmap
                (λ (j) (> (list-ref (list-ref valuations i) j) 0))
                (range m)
            )
        )
        (range n))
)

(assert (feasible-alloc? alloc))
(assert (nonegative-value? valuations))
(assert (identical-EFX-alloc-for-agent-i? 0 alloc))


(define (i-cut-u-choose-for-efx-three-agent an-alloc)
    (if (and 
            (<= (valuation 1 (list-ref an-alloc 0)) (valuation 1 (list-ref an-alloc 1)))
            (<= (valuation 1 (list-ref an-alloc 2)) (valuation 1 (list-ref an-alloc 1)))
        )   ; agent 2 favors (bundle 1)
        (if (<= (valuation 2 (list-ref an-alloc 0)) (valuation 2 (list-ref an-alloc 2)))
            an-alloc ; agent 3 favors (bundle 2)
            (swap-bundle an-alloc 0 2) ; agent 3 favors (bundle 0)
        )
        (
            if (and 
                (<= (valuation 1 (list-ref an-alloc 1)) (valuation 1 (list-ref an-alloc 0)))
                (<= (valuation 1 (list-ref an-alloc 2)) (valuation 1 (list-ref an-alloc 0)))
            ) ; agent 2 favors (bundle 0)
            (if (<= (valuation 2 (list-ref an-alloc 1)) (valuation 2 (list-ref an-alloc 2)))
                (swap-bundle an-alloc 0 1) ; agent 3 favors (bundle 2)
                (swap-bundle (swap-bundle an-alloc 1 2) 0 1) ; agent 3 favors (bundle 1)
            )
            ; agent 2 favors (bundle 3)
            (if (<= (valuation 2 (list-ref an-alloc 0)) (valuation 2 (list-ref an-alloc 1)))
                (swap-bundle an-alloc 1 2) ; agent 3 favors (bundle 1)
                (swap-bundle (swap-bundle an-alloc 0 2) 0 1) ; agent 3 favors (bundle 0)
            )
        )
    )
)

(assert (not (EFX-alloc? (i-cut-u-choose-for-efx-three-agent alloc))))

(evaluate alloc (solve #t))
(evaluate valuations (solve #t))
(evaluate (EF1-alloc-for-agent-i? 1 (i-cut-u-choose-for-efx-three-agent alloc)) (solve #t))
(evaluate (EF1-alloc-for-agent-i? 2 (i-cut-u-choose-for-efx-three-agent alloc)) (solve #t))