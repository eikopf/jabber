#!r6rs

(library (support)
  (export
    ;; BUILTINS
    define lambda quote quasiquote
    + - * / expt mod
    < <= > >=
    fl+ fl- fl* fl/ flexpt
    fl<? fl<=? fl>? fl>=?
    not and or
    equal?
    void
    length append map cons
    vector
    string-length string-append
    ;; PATTERN MATCHING
    match
    match-let*
    match-lambda**
    ;; BOOL
    strict-binary-and
    strict-binary-or
    xor 
    ;; BOXES
    box
    box?
    unbox
    set-box!
    ;; INTEGER
    div*
    ;; IO
    println 
    ;; PANIC
    panic! 
    panic-with-msg! 
    unreachable! 
    todo! 
    ;; STRING
    substring*)

  (import 
    (rnrs base (6)) 
    (rnrs programs (6))
    (rnrs exceptions (6))
    (rnrs arithmetic flonums (6))
    (rnrs io simple (6))
    (only (racket base) void box box? unbox set-box!)
    (only (racket match) match match-let* match-lambda**))

  ;; BOOL
  
  ; strict versions of the lazy operators
  (define (strict-binary-and lhs rhs) (and lhs rhs))
  (define (strict-binary-or  lhs rhs) (or  lhs rhs))

  ; binary XOR is the complement of boolean equality
  (define (xor lhs rhs) 
    (not (boolean=? lhs rhs)))

  ;; INTEGERS

  ; a version of div that returns 0 if the rhs argument is 0
  (define (div* lhs rhs)
    (if (zero? rhs)
        #e0
        (div lhs rhs)))

  ;; IO

  (define (println msg) 
    (display msg)
    (newline))

  ;; PANICKING

  (define (print-and-quit msg)
    (display msg)
    (newline)
    (exit 1))

  (define (panic!) (print-and-quit "panicked"))
  (define (panic-with-msg! msg) (print-and-quit msg))
  (define (unreachable!) (print-and-quit "encountered unreachable code"))
  (define (todo!) (print-and-quit "not yet implemented"))

  ;; STRINGS

  ; a version of substring that returns the empty string if the indices are invalid
  (define (substring* str start end)
    (guard
      (err ((string)))
      (substring str start end))))
  

