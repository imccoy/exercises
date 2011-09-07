(define (frec n)
  (cond ((<= n 3) 1)
        (else (+ (* 1 (frec (- n 1)))
                 (* 2 (frec (- n 2)))
                 (* 3 (frec (- n 3)))))))

(define (fiter f_n-1 f_n-2 f_n-3 n x)
  (cond ((< x n) f_n-1)
      (else (fiter (+ (* 1 f_n-1)
                     (* 2 f_n-2)
                     (* 3 f_n-3))
                   f_n-1
                   f_n-2
                   (+ n 1)
                   x))))

(define (f n)
  (fiter 1 1 1 4 n))

(f 7)
(frec 7)

(map f '(1 2 3 4 5 6 7))
(map frec '(1 2 3 4 5 6 7))