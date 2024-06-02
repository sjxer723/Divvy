#lang rosette

(require "./basic_model.rkt")

(provide EF1-alloc-for-agent-i?)
(provide identical-EF1-alloc-for-agent-i?)
(provide EF1-alloc?)
(provide EFX-alloc-for-agent-i?)
(provide identical-EFX-alloc-for-agent-i?)
(provide EFX-alloc?)

; n agents
;;; (define n 3)
; m items
;;; (define m 10)

(define (EF1-alloc-for-agent-i? a-val-matrix i1 an-alloc n m)
    (andmap
      (λ (i2)
        (or
         (ormap
          (λ (j)
            (>= (valuation a-val-matrix i1 (list-ref an-alloc i1) m)
                (valuation a-val-matrix i1
                           (remove-from-set (list-ref an-alloc i2) j) m)))
          (range m))
         (>= (valuation a-val-matrix i1 (list-ref an-alloc i1) m)
             (valuation a-val-matrix i1 (list-ref an-alloc i2) m))))
      (range n))
)

(define (identical-EF1-alloc-for-agent-i? a-val-matrix i1 an-alloc n m)
    (andmap
      (λ (i2) (EF1-alloc-for-agent-i? a-val-matrix i1 (swap-bundle an-alloc i1 i2) n m))
      (range n))
)

(define (EF1-alloc? a-val-matrix an-alloc n m)
  (andmap
   (λ (i1)
     (EF1-alloc-for-agent-i? a-val-matrix i1 an-alloc n m)
    )
   (range n)))

(define (EFX-alloc-for-agent-i? a-val-matrix i1 an-alloc n m)
    (andmap
      (λ (i2)
        (or
         (andmap
          (λ (j)
            (>= (valuation a-val-matrix i1 (list-ref an-alloc i1) m)
                (valuation a-val-matrix i1
                           (remove-from-set (list-ref an-alloc i2) j) m)))
          (range m))
         (>= (valuation a-val-matrix i1 (list-ref an-alloc i1) m)
             (valuation a-val-matrix i1 (list-ref an-alloc i2) m))))
      (range n))
)

(define (identical-EFX-alloc-for-agent-i? a-val-matrix i1 an-alloc n m)
    (andmap
      (λ (i2) (EFX-alloc-for-agent-i? a-val-matrix i1 (swap-bundle an-alloc i1 i2 n) n m))
      (range n))
)

(define (EFX-alloc? a-val-matrix an-alloc n m)
  (andmap
   (λ (i1)
     (EFX-alloc-for-agent-i? a-val-matrix i1 an-alloc n m))
   (range n)))
