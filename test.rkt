#lang racket

(require racket/control)
(require memoize)

(when #f
	(displayln 1) ; []
	(prompt0 ;a
		(displayln 2) ; [a]
		(prompt0 ;b
			(displayln 3) ; [b, a]
			(control0 kb
				(displayln 4) ; [a]
				(kb)
				(displayln "TODO")
				(raise "TODO"))
			(displayln 5) ; [a]
			(control0 ka
				(displayln 6) ; []
				(prompt0 ;a
					(displayln 7) ; [a]
					(prompt0 ;b
						(displayln 8) ; [b, a]
						(ka)
						(displayln "after 1"))
					(displayln "after 2"))
				(displayln "after 3"))
			(displayln "after 4"))
		(displayln "after 5")))

(when #f
	(displayln 1) ; []
	(prompt0 ;a
		(displayln 2) ; [a]
		(prompt0 ;b
			(displayln 3) ; [b, a]
			(control0 kb
				(displayln 4) ; [a]
				(kb)
				(displayln "TODO")
				(raise "TODO"))
			(displayln 5) ; [a]
			(displayln "after 4"))
		(displayln "after 5")))

(define pa (make-continuation-prompt-tag 'a))
(define pb (make-continuation-prompt-tag 'b))
(define pc (make-continuation-prompt-tag 'c))
(define pd (make-continuation-prompt-tag 'd))

(when #f
	(displayln 1)
	(prompt0-at pa
		(displayln 2)
		(control0-at pa ka
			(displayln 3)
			(prompt0-at pb
				(displayln 4)
				(ka)
				(error "not here"))
			(displayln 8))
		(displayln 5)
		(control0-at pb kb
			(displayln 6)
			1
			(displayln 7))
		(error "not here"))
	(displayln 9))

(when #f
	(define ka1 (prompt0-at pa
		(prompt0-at pb
			(control0-at pb kb1
				#f)
			(control0-at pa ka1
				#f)
			)
		))
	(ka1)
	)

(define/memo (prompt-tag key) (make-continuation-prompt-tag key))
(define ptk (make-continuation-mark-key 'prompt-tag))
(define-syntax (in-frame stx)
	(syntax-case stx ()
		[(_ tag body ...)
			#'(prompt0-at (prompt-tag 'tag)
				(with-continuation-mark ptk 'tag
					(begin body ...)))]))
(define-syntax (jump-out stx)
	(syntax-case stx ()
		[(_ tag k body ...)
			#'(control0-at (prompt-tag 'tag) k body ...)]))
(define i 0)
(define (debug [v #f])
	(displayln (list i v (continuation-mark-set->list (current-continuation-marks) ptk)))
	(set! i (+ i 1)))

(when #f
	; goal: introduce a prompt inside a prompt such that the new one still exists after the old one

	(debug 1) ; []
	(in-frame a
		(debug 2) ; [a]
		(in-frame b
			(debug 3) ; [b, a]
			(in-frame c
				(debug 4) ; [c, b, a]
				(jump-out a ka1
					(debug 5) ; []
					(in-frame d
						(debug 6) ; [d]
						(ka1)
						(debug 7)
					)
					(debug 8)
				)
				(debug 9) ; [c, b, a, d]
			)
			(debug 10) ; [b, a, d]
		)
		(debug 11)
	)
	(debug 12)
)

(when #t
	(debug 1)
	(in-frame a
		(debug 2)
		(jump-out a ka
			(debug 3)
			(in-frame a
				(debug 4)
				(ka)
				(debug 5))
			(debug 6))
		(debug 7)
		(jump-out a ka
			(debug 8)
			(ka)
			(debug 9))
		(debug 10))
	(debug 11))
