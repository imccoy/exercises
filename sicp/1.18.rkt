; a * b = (a/2) * b*2
; a * b = a + a * b-1

(define (double x) (* x 2))

(define (halve x) (/ x 2))

(define (mult x y a)
  (cond ((= x 1) (+ a y))
        ((even? x) (mult (halve x) (double y) a))
        (else (mult (- x 1) y (+ a y)))))
                   

(mult 7 4 0)
(* 7 4)
(mult 5 15 0)
(mult 7 10 0)