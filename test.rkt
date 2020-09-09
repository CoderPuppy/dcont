#lang racket

(require racket/control)

; (displayln 1) ; []
; (prompt0 ;a
; 	(displayln 2) ; [a]
; 	(prompt0 ;b
; 		(displayln 3) ; [b, a]
; 		(control0 kb
; 			(displayln 4) ; [a]
; 			(kb)
; 			(displayln "TODO")
; 			(raise "TODO"))
; 		(displayln 5) ; [a]
; 		(control0 ka
; 			(displayln 6) ; []
; 			(prompt0 ;a
; 				(displayln 7) ; [a]
; 				(prompt0 ;b
; 					(displayln 8) ; [b, a]
; 					(ka)
; 					(displayln "after 1"))
; 				(displayln "after 2"))
; 			(displayln "after 3"))
; 		(displayln "after 4"))
; 	(displayln "after 5"))

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
	(displayln "after 5"))
