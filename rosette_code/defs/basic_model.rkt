#lang rosette

;;; (provide n)
;;; (provide m)
(provide create-sym-list)
(provide create-valuations)
(provide valuation)
(provide alloc)
(provide swap-bundle)
(provide remove-from-set)
(provide feasible-alloc?)
(provide nonegative-value?)

; n agents
;;; (define n 3)
; m items
;;; (define m 10)

(define (create-sym-list n)
    (for/list ([i (in-range n)])
        (define-symbolic* xi real?) xi))

(define (create-valuations n m)
    (for/list ([i (in-range n)]) (create-sym-list m)))

(define (alloc n m)
    (map (λ (i)
         (define-symbolic* x boolean? #:length m)
         x)
       (range n)))

(define (swap-bundle an-alloc i j n) 
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

(define (feasible-alloc? an-alloc n m)
  (andmap
   (λ (j)  
     (= (count-trues (map (λ (i) (list-ref (list-ref an-alloc i) j)) (range n))) 1))
   (range m)))

(define (valuation a-val-matrix i a-set m)
  (apply + (for/list ([k (range m)])
             (if (list-ref a-set k)
                 (list-ref (list-ref a-val-matrix i) k) 0))))

(define (nonegative-value? a-val-matrix n m)
    (andmap
        (λ (i)
            (andmap
                (λ (j) (> (list-ref (list-ref a-val-matrix i) j) 0))
                (range m)
            )
        )
        (range n))
)

(define (remove-from-set a-set j)
    (map (λ (i) (if (= i j) #f (list-ref a-set i))) (range (length a-set)))
)
