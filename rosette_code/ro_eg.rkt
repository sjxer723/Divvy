#lang rosette

; m items
(define m 5)
; n agents
(define n 4)

(define alloc
  (map (λ (i)
         (define-symbolic* x boolean?
           #:length n)
         x)
       (range m)))

(define (count-trues l)
  (apply
   +
   (map
    (λ (b) (if b 1 0))
    l)))

(define (feasible-alloc? an-alloc)
  (andmap
   (λ (i)
     (= (count-trues (list-ref an-alloc i)) 1))
   (range m)))

(define (valuation i a-set) (count-trues a-set))

(define (remove-from-set a-set j)
  (map (λ (i) (if (= i j) #f (list-ref a-set i))) (range (length a-set))))

(define (EF1-alloc? an-alloc)
  (andmap
   (λ (i1)
     (andmap
      (λ (i2)
        (or
         (ormap
          (λ (j)
            (>= (valuation i1 (list-ref an-alloc i1))
                (valuation i1
                           (remove-from-set
                            (list-ref an-alloc i2)
                            j))))
          (range m))
         (>= (valuation i1 (list-ref an-alloc i1))
             (valuation i1
                        (list-ref an-alloc i2)))))
      (range n)))
   (range n)))

(assert (feasible-alloc? alloc))
(assert (EF1-alloc? alloc))

(evaluate
 alloc
 (solve #t))