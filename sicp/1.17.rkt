(define (double x) (* x 2))

(define (halve x) (/ x 2))

(define (mult x y)
  (cond ((= x 1) y)
        ((even? x) (mult (halve x) (double y)))
        (else (+ y (mult (- x 1) y)))))

(mult 7 4)
(* 7 4)
(mult 5 15)