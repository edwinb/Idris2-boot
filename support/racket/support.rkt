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
    (vector 0 #f #f x)))

(define either-right
  (lambda (x)
    (vector 1 #f #f x)))

(define blodwen-error-quit
  (lambda (msg)
    (display msg)
    (newline)
    (exit 1)))

;; Buffers

(define (blodwen-new-buffer size)
  (make-bytevector size 0))

(define (blodwen-buffer-size buf)
  (bytevector-length buf))

(define (blodwen-buffer-setbyte buf loc val)
  (bytevector-u8-set! buf loc val))

(define (blodwen-buffer-getbyte buf loc)
  (bytevector-u8-ref buf loc))

(define (blodwen-buffer-setint buf loc val)
  (bytevector-s32-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getint buf loc)
  (bytevector-s32-ref buf loc (native-endianness)))

(define (blodwen-buffer-setdouble buf loc val)
  (bytevector-ieee-double-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getdouble buf loc)
  (bytevector-ieee-double-ref buf loc (native-endianness)))

(define (blodwen-stringbytelen str)
  (bytevector-length (string->utf8 str)))

(define (blodwen-buffer-setstring buf loc val)
  (let* [(strvec (string->utf8 val))
         (len (bytevector-length strvec))]
    (bytevector-copy! strvec 0 buf loc len)))

(define (blodwen-buffer-getstring buf loc len)
  (let [(newvec (make-bytevector len))]
    (bytevector-copy! buf loc newvec 0 len)
    (utf8->string newvec)))

(define (blodwen-buffer-copydata buf start len dest loc)
  (bytevector-copy! buf start dest loc len))

(define (blodwen-readbuffer-bytes h buf loc max)
  (with-handlers
    ([(lambda (x) #t) (lambda (exn) -1)])
    (get-bytevector-n! h buf loc max)))

(define (blodwen-readbuffer h)
  (with-handlers
    ([(lambda (x) #t) (lambda (exn) (make-bytevector 0))])
    (get-bytevector-all h)))

(define (blodwen-writebuffer h buf loc max)
  (with-handlers
    ([(lambda (x) #t) (lambda (exn) -1)])
    (put-bytevector h buf loc max)))

;; Files : Much of the following adapted from idris-chez, thanks to Niklas
;; Larsson

;; All the file operations are implemented as primitives which return
;; Either Int x, where the Int is an error code
(define (blodwen-error-code x)
    (cond
        ((eq? x (lookup-errno 'ENOENT)) 3)
        ((eq? x (lookup-errno 'EACCES)) 4)
        ((eq? x (lookup-errno 'EEXIST)) 5)
        (else (+ x 256))))

;; If the file operation raises an error, catch it and return an appropriate
;; error code
(define (blodwen-file-op op)
  (with-handlers
       ([exn:fail:filesystem:errno?
          (lambda (exn) (either-left (blodwen-error-code
                                (car (exn:fail:filesystem:errno-errno exn)))))]
        [exn:fail:filesystem?
          (lambda (exn) (either-left 255))]
        )
      (either-right (op))))

(define (blodwen-putstring p s)
    (if (port? p) (write-string p s) void)
    0)

(define (blodwen-open file mode bin)
    (define tc (if (= bin 1) #f (make-transcoder (utf-8-codec))))
    (define bm (buffer-mode line))
    (case mode
        (("r") (open-file-input-port file (file-options) bm tc))
        (("w") (open-file-output-port file (file-options no-fail) bm tc))
        (("wx") (open-file-output-port file (file-options) bm tc))
        (("a") (open-file-output-port file (file-options no-fail no-truncate) bm tc))
        (("r+") (open-file-input/output-port file (file-options no-create) bm tc))
        (("w+") (open-file-input/output-port file (file-options no-fail) bm tc))
        (("w+x") (open-file-input/output-port file (file-options) bm tc))
        (("a+") (open-file-input/output-port file (file-options no-fail no-truncate) bm tc))
        (else (raise (make-i/o-error)))))


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

;; Directories

(define (blodwen-current-directory)
  (path->string (current-directory)))

(define (blodwen-change-directory dir)
  (if (directory-exists? dir)
      (begin (current-directory dir) 1)
      0))

(define (blodwen-create-directory dir)
  (blodwen-file-op (lambda () (make-directory dir))))

; Scheme only gives a primitive for reading all the files in a directory,
; so this is faking the C interface!
(define (blodwen-open-directory dir)
  (blodwen-file-op (lambda () (box (directory-list dir)))))

(define (blodwen-close-directory dir) '()) ; no-op, it's not really open

(define (blodwen-next-dir-entry dir)
  (let [(dlist (unbox dir))]
    (if (null? dlist)
      (either-left 255)
      (begin (set-box! dir (cdr dlist))
             (either-right (path->string (car dlist)))))))

;; Threads

(define blodwen-thread-data (make-thread-cell #f))

(define (blodwen-thread p)
    (thread (lambda () (p (vector 0)))))

(define (blodwen-get-thread-data)
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

(define (blodwen-args)
  (define (blodwen-build-args args)
    (if (null? args)
        (vector 0 '())
        (vector 1 '() (car args) (blodwen-build-args (cdr args)))))
    (blodwen-build-args
      (cons (path->string (find-system-path 'run-file))
            (vector->list (current-command-line-arguments)))))

(define (blodwen-system cmd)
  (if (system cmd)
      0
      1))
