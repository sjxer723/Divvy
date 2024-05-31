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

(define valuations
  (list (list 1 2 3 4 5)
        (list 5 4 3 2 1)
        (list 3 3 3 3 3)
        (list 3 3 3 3 3)))

(define (valuation i j alloc)
  (apply + (for/list ([k (range m)])
             (* (if (list-ref (list-ref alloc k) j) 1 0)
                (list-ref (list-ref valuations i) k)))))

(define (remove-from-set a-set j)
  (map (λ (i) (if (= i j) (build-list n (lambda (x) #f)) (list-ref a-set i))) (range (length a-set))))

(define (EF1-alloc? an-alloc)
  (andmap
   (λ (i1)
     (andmap
      (λ (i2)
        (or
         (ormap
          (λ (j)
            (>= (valuation i1 i1 an-alloc)
                (valuation i1 i2
                           (remove-from-set
                            an-alloc
                            j))))
          (range m))
         (>= (valuation i1 i1 an-alloc)
             (valuation i1 i2
                        an-alloc))))
      (range n)))
   (range n)))

(assert (feasible-alloc? alloc))
(assert (EF1-alloc? alloc))

(evaluate
 alloc
 (solve #t))