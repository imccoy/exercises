(define (square x)
  (* x x))

(define (cube x)
  (* x x x))

(define (cbrt-iter guess x)
  (if (good-enough? guess x)
      guess
      (cbrt-iter (improve guess x)
                 x)))

(define (improve guess x)
  (/ (+ (/ x (square guess)) (* 2 guess)) 3))

(define (average x y)
  (/ (+ x y) 2))

(define (good-enough? guess x)
  (< (abs (- (cube guess) x)) 0.001))

(define (mcbrt x)
  (cbrt-iter 1.0 x))

(mcbrt 125)