#!r6rs

;; runtime support
;; ----------------
;; this file is effectively the glue underneath the core library, and is
;; loaded by absolutely every jabber program before execution

;; PANICKING FUNCTIONS

(define print-and-quit
  (lambda [msg]
    (display msg)
    (newline)
    (exit 1)))

(define panic! (print-and-quit "panicked"))
(define panic-with-msg! print-and-quit)
(define unreachable! (print-and-quit "encountered unreachable code"))
(define todo! (print-and-quit "not yet implemented"))

;; STRINGS

; a version of substring that returns the empty string if the indices are bad
(define substring*
  (lambda [str start end]
    (guard 
      (err ((string)))
      (substring str start end))))

;; INTEGERS

; a version of div that returns 0 if the rhs argument is 0
(define div*
  (lambda [lhs rhs]
    (if (zero? rhs) 
      #e0 
      (div lhs rhs))))
