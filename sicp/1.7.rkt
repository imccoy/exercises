(define (square x)
  (* x x))

(define (sqrt-iter oldguess guess x)
  (if (good-enough? oldguess guess)
      guess
      (sqrt-iter guess (improve guess x)
                 x)))

(define (improve guess x)
  (average guess (/ x guess)))

(define (average x y)
  (/ (+ x y) 2))

(define (good-enough? oldguess guess)
  (< (/ (abs (- oldguess guess)) guess) 0.0001))

(define (msqrt x)
  (sqrt-iter 0 1.0 x))

(msqrt 5)