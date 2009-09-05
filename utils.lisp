;; From Graham's On Lisp
(defmacro with-gensyms (syms &body body)
  `(let ,(mapcar #'(lambda (s) `(,s (gensym))) syms) ,@body))

;; Some macros and functions taken from Doug Hoyte's 'Let Over Lambda'

(defun mkstr (&rest args)
  (with-output-to-string (s)
	(dolist (a args) (princ a s))))

(defun symb (&rest args)
  (values (intern (apply #'mkstr args))))



(defun group (source n)
  (if (zerop n) (error "zero length"))
  (labels ((rec (source acc)
				(let ((rest (nthcdr n source)))
				  (if (consp rest)
					(rec rest (cons
								(subseq source 0 n)
								acc))
					(nreverse
					  (cons source acc))))))
	(if source (rec source nil) nil)))



(defun flatten (x)
  (labels ((rec (x acc)
				(cond ((null x) acc)
					  ((atom x) (cons x acc))
					  (t (rec
						   (car x)
						   (rec (cdr x) acc))))))
	(rec x nil)))

(defun g!-symbol-p (s)
  (and (symbolp s)
	   (> (length (symbol-name s)) 2)
	   (string= (symbol-name s)
				"G!"
				:start1 0
				:end1 2)))



(defmacro defmacro/g! (name args &rest body)
  (let ((syms (remove-duplicates
				(remove-if-not #'g!-symbol-p
							   (flatten body)))))
	`(defmacro ,name ,args
	   (let ,(mapcar
			   (lambda (s)
				 `(,s (gensym ,(subseq
								 (symbol-name s)
								 2))))
			   syms)
		 ,@body))))



(defun o!-symbol-p (s)
  (and (symbolp s)
	   (> (length (symbol-name s)) 2)
	   (string= (symbol-name s)
				"O!"
				:start1 0
				:end1 2)))

(defun o!-symbol-to-g!-symbol (s)
  (symb "G!"
		(subseq (symbol-name s) 2)))



(defmacro defmacro! (name args &rest body)
  (let* ((os (remove-if-not #'o!-symbol-p args))
		 (gs (mapcar #'o!-symbol-to-g!-symbol os)))
	`(defmacro/g! ,name ,args
				  `(let ,(mapcar #'list (list ,@gs) (list ,@os))
					 ,(progn ,@body)))))
;; (defmacro defmacro! (name args &rest body)
;;   (let* ((os (remove-if-not #'o!-symbol-p (flatten (list args body))))
;; 		 (gs (mapcar #'o!-symbol-to-g!-symbol os)))
;; 	`(defmacro/g! ,name ,args
;; 				  `(let ,(mapcar #'list (list ,@gs) (list ,@os))
;; 					 ,(progn ,@body)))))
;; End of Doug Hoyte's stuff

(defmacro! db-lambda (args &body body)
  "A lambda that takes a destructuring lambda list"
  `(lambda (,g!x)
	 (destructuring-bind ,args ,g!x
	   ,@body)))
;; (defmacro db-lambda (args &body body)
;;   "A lambda that takes a destructuring lambda list"
;;   (let ((x (gensym)))
;;     `(lambda (,x)
;;        (destructuring-bind ,args ,x
;; 	 ,@body))))
(defmacro aif (test-exp true-exp false-exp)
  `(let ((it ,test-exp))
     (if it ,true-exp ,false-exp)))

(defmacro awhen (test-exp then-exp)
  `(let ((it ,test-exp))
     (when it ,then-exp)))

(defmacro dbind (&rest stuff)
  `(destructuring-bind ,@stuff))

(defun span (pred list)
  (aif (position-if-not pred list)
       (cons (subseq list 0 it) (subseq list it))
       (cons (copy-seq list) nil)))

(defmacro memoised-defun (fn args &body body)
  (let ((cache (make-hash-table :test #'equalp)))
    `(defun ,fn ,args
       (aif (gethash (list ,@args) ,cache)
	    it
	    (setf (gethash (list ,@args) ,cache) (progn ,@body))))))

(defun from-to (m n)
  (loop for i from m to (1- n) collect i))

(defun 0-to (n) (from-to 0 n))

(defun partition (pred list)
  (cons
   (remove-if-not pred list)
   (remove-if pred list)))

(defun tree-size (tree)
  (apply #'+ (mapcar (lambda (s) (if (consp s) (tree-size s) 1)) tree)))

(defmacro all-non-null (&rest forms)
  `(and ,@forms))

(defun copy-hash-table (tbl)
  (let ((copied-tbl (make-hash-table :test (hash-table-test tbl))))
    (maphash (lambda (k v) (setf (gethash k copied-tbl) v)) tbl)
    copied-tbl))

(defun hash-table-keys (tbl)
  (let ((keys '()))
    (maphash (lambda (k v) (declare (ignore v)) (push k keys)) tbl)
    keys))
(declaim (ftype (function (function &rest t) function) curry)
           (inline curry))
(defun curry (function &rest args)
  (lambda (&rest more-args)
	(apply function (append args more-args))))
(defun curry-at-end (function &rest args)
  (lambda (&rest more-args)
	(apply function (append more-args args))))
			  
(defmacro abbrev (short long)
  	`(defmacro ,short (&rest args-and-body)
	   	`(,',long ,@args-and-body)))

(defmacro abbrevs (&rest names)
  `(progn
	 ,@(mapcar (lambda (pair) `(abbrev ,@pair))
			   (group names 2))))
(defun compose (&rest fns)
  (if fns
      (let ((fn1 (car (last fns)))
	    (fns (butlast fns)))
	#'(lambda (&rest args)
	    (reduce #'funcall fns
		    :from-end t
		    :initial-value (apply fn1 args))))
    #'identity))

(abbrevs c curry
		 ca curry-at-end
		 o compose
		 f funcall)

(defun set-equals (set1 set2 &key (test #'equal))
  (= (length set1) (length set2) (length (intersection set1 set2 :test test))))

(defun tree-equivalent (tree1 tree2 &key (test #'eql))
  (labels ((recurse (x y) 
					(cond ((and (consp x) (consp y)) (set-equals x y :test #'recurse))
						  ((and (atom x) (atom y)) (funcall test x y))
						  (t nil))))
	(recurse tree1 tree2)))

(define-test test-tree-equivalent
  (assert-true
	(tree-equivalent '(a b c) '(c b a) :test #'eq))
  (assert-true
	(tree-equivalent '(a (b 3) c) '(c (3 b) a) :test #'eq))
  (assert-true
	(tree-equivalent '(a (b 3) (c (4 5 s))) '(((s 4 5) c) (3 b) a) :test #'eq))
  )

(run-tests test-tree-equivalent)

(defmacro! until (pred &body body)
  `(let ((,g!result))
	 (tagbody ,g!block
			  (if (not ,pred)
				(progn
				  (setq ,g!result (progn ,@body))
				  (go ,g!block))))
	 ,g!result))

(define-test test-until
  (let ((x 0))
	(assert-equal (until (>= x 20)
					(incf x)
					(* x 10)) 
				  200)
	(assert-equal x 20)))

(run-tests test-until)
;; #{#~(fn arg1 arg2) fn2}

(defun |#_-reader| (stream sub-char numarg)
  "Reader macro giving a shorthand for anonymous functions, 
  #n$(...) expands to (lambda ($1 $2 ... $n) (...))"
  (declare (ignore sub-char))
  (unless numarg (setq numarg 1))
  (let ((syms (if (> numarg 1)
				(loop for i from 1 to numarg
				  collect (symb '_ i))
				(list (symb '_)))))
	`(lambda ,syms
	   (declare (ignorable ,@syms))
	   ,(read stream t nil t))))

(set-dispatch-macro-character
  #\# #\_ #'|#_-reader|)




(defun foldr (fn init args)
  (reduce fn args :initial-value init :from-end t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Reader macros for curry and compose
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun to-function-symbol (function-exp)
  "Used to allow cleaner syntax for representing functions in curry and compose reader macros. 
  Symbols in a function position (any term for compose, the first only for curry) will be prepended
  with #' unless they begin with an underscore. This is intended for variables with function values.
  Lambda expressions are unchanged, so for example"
  (if (symbolp function-exp)
	(if (string= "_" (symbol-name function-exp) :start2 0 :end2 1)
	  (symb (subseq (symbol-name function-exp) 1))
	  `#',function-exp)
	function-exp))

(defun add-curry-syntax ()
  "Reader macro for currying functions. Works like, e.g.
  	(macroexpand '[* 10 15]) =>
		#'(LAMBDA (&REST MORE-ARGS) (APPLY #'* (APPEND (LIST 10 15) MORE-ARGS)))
"
  (set-macro-character #\] (get-macro-character #\)))
  (set-macro-character 
	#\[
	(lambda (stream char)
	  (declare (ignore char))
	  (dbind (fn . args) (read-delimited-list #\] stream t)
			 (let ((genargs) (allargs))
 			   (dolist (s args)
				 (when (and (symbolp s) (string= "_" (symbol-name s)))
				   (setq s (gensym))
				   (push s genargs))
				 (push s allargs))
			   `(lambda (,@(reverse genargs) &rest more-args) 
				  (apply ,(to-function-symbol fn) (append (list ,@(reverse allargs)) more-args)))) ) ))) 



(defun add-compose-syntax ()
  "Reader macro for composing functions. E.g.

  * (macroexpand '(let ((foo #'1+ )) {cos _foo (lambda (x y) (+ x y))}))
  		(LET ((FOO #'1+))
	     	(LAMBDA (&REST #:G2729)
			     (FUNCALL #'COS (FUNCALL FOO (APPLY (LAMBDA (X Y) (+ X Y)) #:G2729)))))
  "
  (set-macro-character #\} (get-macro-character #\)))
  (set-macro-character 
	#\{
	(lambda (stream char)
	  (declare (ignore char))
	  (let ((fns  (mapcar #'to-function-symbol (read-delimited-list #\} stream t))))
		(if fns
		  (with-gensyms (args)
						`(lambda (&rest ,args) ,(foldr (c #'list 'funcall)
													   `(apply ,(car (last fns)) ,args)
													   (butlast fns))))
		  #'identity)

		))))

(add-curry-syntax)
(add-compose-syntax)
(defun trunc (n list)
  (subseq list 0 (min n (length list))))
