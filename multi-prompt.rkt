#lang racket

(require racket/match)
(require racket/control)

(define (handle tag res)
	(match res
		[(cons #f v) v]
		[(cons (== tag) (cons k f))
			(reset-mp tag f (lambda (x)
				(handle tag (k x))))]
		[(cons tag2 (cons k f))
			(shift k2 (cons tag2 (cons
				(lambda (x)
					(k2 (handle tag (k x))))
				f)))]))
(define (reset-mp tag f . args)
	(handle tag (reset (cons #f (apply f args)))))
(define (shift-mp tag f)
	(shift k (cons tag (cons k f))))
