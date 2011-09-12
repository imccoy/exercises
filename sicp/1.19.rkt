; Tpq(a,b) = (bq + aq + ap, bp + aq)
; Tpq(Tpq(a,b)) = Tpq(bq + aq + ap, bp + aq)
;               = Tpq(q(bp + aq) + q(bq + aq + ap) + p(bq + aq + ap), p(bp + aq) + q(bq + aq + ap))
; q(bp + aq) + q(bq + aq + ap) + p(bq + aq + ap) = bpq + aqq + bqq + aqq + apq + bpq + apq + app
;                                                = pp(a) + pq(b + a + b + a) + qq(a + b + a)
;                                                = a(pp + pq + pq + qq + qq) + b(pq + pq + qq) 
; Tmn(a,b) = (bn + an + am, bm + an) => n = (pq + pq + qq)
;                                     n + m = (pp + pq + pq + qq + qq)
;                                      m = (pp + pq + pq + qq + qq) - (pq + pq + qq)
;                                        = pp + qq
; p(bp + aq) + q(bq + aq + ap) = bpp + aqp + bqq + aqq + apq
;                              = pp(b) + pq(a + a) + qq(a + b)
;                              = a(pp + pq + pq + qq) + b(qq + pp)



(define (fib n)
  (fib-iter 1 0 0 1 n))
(define (fib-iter a b p q count)
  (cond ((= count 0) b)
        ((even? count)
         (fib-iter a
                   b
                   (+ (* q q) (* p p))                ; compute p'
                   (+ (* 2 p q) (* q q))              ; compute q'
                   (/ count 2)))
        (else (fib-iter (+ (* b q) (* a q) (* a p))
                        (+ (* b p) (* a q))
                        p
                        q
                        (- count 1)))))

(map fib '(0 1 2 3 4 5 6 7 8 9 0))