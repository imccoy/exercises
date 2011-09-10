; b^n     = (b*b)^(n/2), n even
; b^n     = b * b^(n-1), n odd

; (b^(n/2))^2 = (b^2)^(n/2)

; a * b^n = a * (b^2)^(n/2), n even 
; a * b^n = b 

(define (mexpt b n a )
  (cond ((= n 1) (* a b))
        ((even? n) (mexpt (* b b) (/ n 2) a))
        (else      (mexpt b (- n 1) (* a b)))))

(mexpt 6 8 1)
(expt 6 8)