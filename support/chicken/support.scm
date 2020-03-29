(define blodwen-read-args (lambda (desc)
  (case (vector-ref desc 0)
    ((0) '())
    ((1) (cons (vector-ref desc 2)
               (blodwen-read-args (vector-ref desc 3)))))))
(define b+ (lambda (x y bits) (remainder (+ x y) (expt 2 bits))))
(define b- (lambda (x y bits) (remainder (- x y) (expt 2 bits))))
(define b* (lambda (x y bits) (remainder (* x y) (expt 2 bits))))
(define b/ (lambda (x y bits) (remainder (/ x y) (expt 2 bits))))

(define blodwen-shl (lambda (x y) (arithmetic-shift x y)))
(define blodwen-shr (lambda (x y) (arithmetic-shift x (- y))))
(define blodwen-and (lambda (x y) (bitwise-and x y)))
(define blodwen-or (lambda (x y) (bitwise-or x y)))
(define blodwen-xor (lambda (x y) (bitwise-xor x y)))

(define cast-num
  (lambda (x)
    (if (number? x) x 0)))
(define destroy-prefix
  (lambda (x)
    (if (eqv? x "") ""
      (if (eqv? (string-ref x 0) #\#) "" x))))
(define cast-string-int
  (lambda (x)
    (floor (cast-num (string->number (destroy-prefix x))))))
(define cast-string-double
  (lambda (x)
    (cast-num (string->number (destroy-prefix x)))))
(define string-cons (lambda (x y) (string-append (string x) y)))
(define get-tag (lambda (x) (vector-ref x 0)))
(define string-reverse (lambda (x)
  (list->string (reverse (string->list x)))))
(define (string-substr off len s)
    (let* ((l (string-length s))
          (b (max 0 off))
          (x (max 0 len))
          (end (min l (+ b x))))
          (substring s b end)))

(define either-left
  (lambda (x)
    (vector 0 #f #f x)))

(define either-right
  (lambda (x)
    (vector 1 #f #f x)))

(define blodwen-error-quit
  (lambda (msg)
    (display msg)
    (newline)
    (exit 1)))

;; Files: Much of the following adapted from idris-chez, thanks to Niklas
;; Larsson

;; All the file operations are implemented as primitives which return
;; Either Int x, where the Int is an error code

;; If the file operation raises an error, catch it and return an appropriate
;; error code
(define (blodwen-file-op op)
  (handle-exceptions exn
        (begin (either-left 255)) ; TODO: Calculate proper code!
        (either-right (op))))

(define (blodwen-get-n n p)
    (if (input-port? p) (get-string-n p n) ""))

(define (blodwen-putstring p s)
    (if (output-port? p) (put-string p s) void)
    0)

(define (blodwen-open file mode bin)
    (cond
        ((string=? mode "r") (open-input-file file))
        ((string=? mode "w") (open-output-file file))
        (else (abort "I haven't worked that one out yet, sorry..."))))

(define (blodwen-close-port p)
    (cond
      ((input-port? p) (close-input-port p))
      ((output-port? p) (close-output-port p))))

(define (blodwen-get-line p)
    (if (port? p)
        (let ((str (read-line p)))
            (if (eof-object? str)
                ""
                (string-append str "\n")))
        void))

(define (blodwen-get-char p)
    (if (port? p)
        (let ((char (read-char p)))
            (if (eof-object? char)
                #\nul
                char))
        void))

(define (blodwen-eof p)
  (if (eof-object? (peek-char p))
      1
      0))

;; Threads

(define (blodwen-thread p)
    (thread-start! (make-thread (lambda () (p (vector 0))))))

(define (blodwen-set-thread-data p)
    (thread-specific-set! (current-thread) p))

(define (blodwen-get-thread-data)
    (thread-specific (current-thread)))

(define (blodwen-mutex) (make-mutex))
(define (blodwen-lock m) (mutex-lock! m))
(define (blodwen-unlock m) (mutex-unlock! m))
(define (blodwen-thisthread) (current-thread))

(define (blodwen-condition) (make-condition-variable))
(define (blodwen-condition-wait c m)
  (mutex-unlock! m c)
  (mutex-lock! m)) ;; lock again, for consistency with other CGs
(define (blodwen-condition-wait-timeout c m t) (mutex-unlock! m c t))
(define (blodwen-condition-signal c) (condition-variable-signal! c))
(define (blodwen-condition-broadcast c) (condition-variable-broadcast! c))

(define (blodwen-sleep s) (sleep s))

(define (blodwen-args)
  (define (blodwen-build-args args)
    (if (null? args)
        (vector 0 '())
        (vector 1 '() (car args) (blodwen-build-args (cdr args)))))
    (blodwen-build-args (argv)))
