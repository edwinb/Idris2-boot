(define blodwen-read-args (lambda (desc)
  (case (vector-ref desc 0)
    ((0) '())
    ((1) (cons (vector-ref desc 2)
               (blodwen-read-args (vector-ref desc 3)))))))
(define b+ (lambda (x y bits) (remainder (+ x y) (expt 2 bits))))
(define b- (lambda (x y bits) (remainder (- x y) (expt 2 bits))))
(define b* (lambda (x y bits) (remainder (* x y) (expt 2 bits))))
(define b/ (lambda (x y bits) (remainder (exact-floor (/ x y)) (expt 2 bits))))

(define blodwen-shl (lambda (x y) (arithmetic-shift x y)))
(define blodwen-shr (lambda (x y) (arithmetic-shift x (- y))))
(define blodwen-and (lambda (x y) (bitwise-and x y)))
(define blodwen-or (lambda (x y) (bitwise-ior x y)))
(define blodwen-xor (lambda (x y) (bitwise-xor x y)))

(define cast-num
  (lambda (x)
    (if (number? x) x 0)))
(define destroy-prefix
  (lambda (x)
    (cond
      ((equal? x "") "")
      ((equal? (string-ref x 0) #\#) "")
      (else x))))
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
    (vector 0 x)))

(define either-right
  (lambda (x)
    (vector 1 x)))

(define blodwen-error-quit
  (lambda (msg)
    (display msg)
    (newline)
    (exit 1)))

(define (blodwen-get-line p)
    (if (port? p)
        (let ((str (read-line p)))
            (if (eof-object? str)
                ""
                str))
        void))

(define (blodwen-get-char p)
    (if (port? p)
        (let ((chr (read-char p)))
            (if (eof-object? chr)
                #\nul
                chr))
        void))

;; Threads

(define blodwen-thread-data (make-thread-cell #f))

(define (blodwen-thread p)
    (thread (lambda () (p (vector 0)))))

(define (blodwen-get-thread-data ty)
  (thread-cell-ref blodwen-thread-data))

(define (blodwen-set-thread-data a)
  (thread-cell-set! blodwen-thread-data a))

(define (blodwen-mutex) (make-semaphore 1))
(define (blodwen-lock m) (semaphore-post m))
(define (blodwen-unlock m) (semaphore-wait m))
(define (blodwen-thisthread) (current-thread))

(define (blodwen-condition) (make-channel))
(define (blodwen-condition-wait c m)
  (blodwen-unlock m) ;; consistency with interface for posix condition variables
  (sync c)
  (blodwen-lock m))
(define (blodwen-condition-wait-timeout c m t)
  (blodwen-unlock m) ;; consistency with interface for posix condition variables
  (sync/timeout t c)
  (blodwen-lock m))
(define (blodwen-condition-signal c)
  (channel-put c 'ready))

(define (blodwen-sleep s) (sleep s))

(define (blodwen-time) (current-seconds))

(define (blodwen-clock-time-utc) (current-time 'time-utc))
(define (blodwen-clock-time-monotonic) (current-time 'time-monotonic))
(define (blodwen-clock-time-duration) (current-time 'time-duration))
(define (blodwen-clock-time-process) (current-time 'time-process))
(define (blodwen-clock-time-thread) (current-time 'time-thread))
(define (blodwen-clock-time-gccpu) 0) ;; unsupported
(define (blodwen-clock-time-gcreal) 0) ;; unsupported
(define (blodwen-is-time? clk) (if (time? clk) 1 0))
(define (blodwen-clock-second time) (time-second time))
(define (blodwen-clock-nanosecond time) (time-nanosecond time))

(define (blodwen-args)
  (define (blodwen-build-args args)
    (if (null? args)
        (vector 0) ; Prelude.List
        (vector 1 (car args) (blodwen-build-args (cdr args)))))
    (blodwen-build-args
      (cons (path->string (find-system-path 'run-file))
            (vector->list (current-command-line-arguments)))))

(define (blodwen-system cmd)
  (if (system cmd)
      0
      1))

;; Randoms
(random-seed (date*-nanosecond (current-date))) ; initialize random seed

(define (blodwen-random-seed s) (random-seed s))
(define blodwen-random
  (case-lambda
    ;; no argument, pick a real value from [0, 1.0)
    [() (random)]
    ;; single argument k, pick an integral value from [0, k)
    [(k) (if (> k 0)
           (random k)
           (raise 'blodwen-random-invalid-range-argument))]))
