(use-package :lisp-unit)

(defun tokens (grammar)
  (remove-duplicates (apply #'append grammar)))

(defun non-terminals (grammar)
  (remove-duplicates (mapcar #'car grammar)))

(defun terminals (grammar) (set-difference (tokens grammar) (non-terminals grammar)))

(defvar grammar-1 '(
		    (E E * B)
		    (E E + B)
		    (E B)
		    (B 0)
		    (B 1)
		    ))

(defvar grammar-2 '(
		    (Z d)
		    (Z X Y Z)
		    (Y)
		    (Y c)
		    (X Y)
		    (X a)))


(defun nullables (grammar)
  "Finds the nullable set of tokens by the applying the recursive rule
  	A token X is nullable if and only if there exists a production 
		X -> Y_1 .. Y_n 
	where each of the Y_i is nullable "
  (loop
	with num-nullables = -1
	and nullables = '()
	do 	(setq num-nullables (length nullables))
		(loop for (lhs . rhs) in grammar
		  if (and (not (member lhs nullables))
				  (every [member _ nullables] rhs)) 
		  do (push lhs nullables))
	until (= num-nullables (length nullables))
	finally (return nullables)))

(define-test test-nullables
  (let ((set-eql (ca #'set-equals :test #'eql))) 
	(assert-equality set-eql '(Y X) (nullables grammar-2))
	(assert-equality set-eql  '() (nullables grammar-1))))

(run-tests test-nullables)

(defun member-pred (set &key (test #'equal))
  #_(member _ set :test test))

(defun create-list-map (keys)
  (mapcar #'list keys))

(defun list-map-value (key map)
  (cdr (assoc key map)))

(defun add-to-list-map (key map new-values)
  (rplacd (assoc key map)
	  (union new-values
		 (list-map-value key map)
		 :test #'equalp)))

(defun add-value-to-list-map (key map value)
  (add-to-list-map key map (list value)))

(defun list-maps-equal (lm-1 lm-2)
  (let ((keys1 (mapcar #'car lm-1))
	(keys2 (mapcar #'car lm-2)))
    (labels ((set-equals (set1 set2)
	       (= (length set1)
		  (length set2)
		  (length (intersection set1 set2)))))
      (and (set-equals keys1 keys2)
	   (every (lambda (k)
		    (set-equals (list-map-value k lm-1)
				(list-map-value k lm-2)))
		  keys1)))))
(defun alist-to-function (alist)
  (lambda (x)
    (aif (assoc x alist)
	 (cdr it)
	 (error (format nil "~a not found" x)))))

(defun firsts (grammar)
  (let ((nullable-p (member-pred (nullables grammar))))
	(loop with firsts-size = 0
		  and firsts = (make-list-multi-map :key-test #'eql :value-test #'eql)
		  initially (loop for x in (terminals grammar)
						  do (f firsts :add x x))
		  do (loop 
			   for (X . Y_s) in grammar
			   do (dbind (nullable_Y_s . rest_Ys)
						 (span nullable-p Y_s)
						 (dolist (y (append nullable_Y_s (awhen (car rest_Ys) (list it))))
						   (f firsts :add-all X (f firsts :get y)))))
		  (if (= firsts-size (f firsts :size))
			(return (f firsts :map))
			(setq firsts-size (f firsts :size))))))

(define-test test-firsts
  (labels ((check (grammar expected)
				  (assert-true (tree-equivalent (firsts grammar) expected))))	
	(check '((Z)) '())
	(check '((A b)) '((A b)(b b)))
	(check '((A b) (A X) (X) (X c))
		   '((A b c) (X c) (b b) (c c)))
	))

(run-tests test-firsts)

(defun join-all (lists-1 lists-2)
  (loop for l1 in lists-1 nconcing
	(loop for l2 in lists-2 collecting
	  (append l1 l2))))

(defun on-all-pairs (fn lists-1 lists-2)
  (loop for l1 in lists-1 nconcing
	(loop for l2 in lists-2 collecting
	  (funcall fn l1 l2))))

(defun truncate-list (k list)
  (subseq list 0 (min k (length list))))

(defun firsts-k (grammar k)
  "Maps each token to the set of distinct terminal it can expand to, upto
  at most length k. Result is returned as an assoc list with token keys
  and lists of expansions as values.
  TODO - rewrite this awful comment"
  (let ((f-k (make-list-multi-map))
		(saved-size))
	(with-multi-map f-k
	  (mapc #_(f-k-add _ (list _)) (terminals grammar))
	  (until (eq saved-size f-k-size)
		(setq saved-size f-k-size)
		(loop for (X . Y-s) in grammar
		  do (f-k-add-all X (foldl [on-all-pairs { [trunc k] append}] 
								   '(nil)
								   (mapcar #'f-k-get Y-s)))))
	  (f-k-map))))


(defun follows-k (grammar k)
  (labels ((full-length-p (lst) (>= (length lst) k)))
    (loop with f-k-1 = '()
       and f-k-2 = (create-list-map (tokens grammar))
       initially (loop for x in (terminals grammar)
		    do (add-value-to-list-map x f-k-2 (list x)))
       do (loop for (X . Y_s) in grammar
	     do (let ((y-first-ks (mapcar (lambda (y) (list-map-value y f-k-2)) Y_s)))
		  
		  (when (all-non-null y-first-ks)
		    (add-to-list-map
		     X
		     f-k-2
		     (reduce (lambda (&rest forms)
			       (when forms
				 (dbind (forms1 forms2) forms
					(dbind (forms1-a . forms1-b)
					  (partition #'full-length-p forms1)
					  (append forms1-a
						  (mapcar (curry #'truncate-list k)
							  (join-all forms1-b forms2))))
					)))
			     y-first-ks)))))
	 (if (=  (tree-size f-k-1) (tree-size f-k-2))
	     (return f-k-1)
	     (setq f-k-1 (copy-tree f-k-2))))))



	
;; Follows algorithm for 1 element -
;; For each production X -> Y_1 ... Y_n
;; For 1 <= i <= n, if Y_i+1, ..., Y_n are all nullable then
;; follows(Y_i) contains follows(X)
;; for each j, i < j <= n,
;;    if Y_i+1, ..., Y_j-1 are all nullable then
;;  	follows(y_i) contains first(Y_j)



;; Follows algorithm for k element -
;; For each production X -> Y_1 ... Y_n
;; For 1 <= i <= n, if Y_i+1, ..., Y_n are all nullable then
;; follows(Y_i) contains follows(X)
;; for each j, i < j <= n,
;;    if Y_i+1, ..., Y_j-1 are all nullable then
;;  	follows(y_i) contains first(Y_j)
(defun follows (grammar)
  (let ((nullable-p (member-pred (nullables grammar)))
	(firsts (firsts grammar)))
    (loop
       with follows-1 = '()
       and follows-2 = (create-list-map (tokens grammar))
       do
	 (loop 
	    for (X . Y_s) in grammar
	    do (loop for (Y_i . Y_i+s) on Y_s
		  do (when (every nullable-p Y_i+s)
		       (add-to-list-map Y_i follows-2
					(list-map-value X follows-2)))
		    (dbind (nullable_Y_s . rest_Ys)
		    	   (span nullable-p Y_i+s)
		    	   (dolist (y (append nullable_Y_s (awhen (car rest_Ys) (list it))))
			     
		    	     (add-to-list-map Y_i follows-2
					      (list-map-value y firsts))))))
	 (if (list-maps-equal follows-1 follows-2)
	     (return follows-1)
	     (setq follows-1 (copy-tree follows-2))))))


(defun all-pairs (l1 l2)
  (apply #'append
	 (mapcar (lambda (x) (mapcar (lambda (y) (cons x y)) l2)) l1)))

(defun ll-parsing-table (grammar)
  (let ((firsts (alist-to-function (firsts grammar)))
	(follows (alist-to-function (follows grammar)))
	(nullable-p (member-pred (nullables grammar))))
    (labels ((exp-firsts (exp &optional acc)
	       (if (null exp)
		   acc
		   (dbind (y . ys) exp
			  (if (funcall nullable-p y)
			      (exp-firsts ys (union acc (funcall firsts y)))
			      (union acc (funcall firsts y)))))))
      (loop for (A . alpha) in (all-pairs (non-terminals grammar) (terminals grammar))
	 collect (cons (cons A alpha)
		       (remove-if-not (db-lambda (X . Y_s)
					(and (equal X A)
					     (or (member alpha (exp-firsts Y_s))
						 (and (every nullable-p Y_s)
						      (member alpha (funcall follows X))))))
				      grammar))))))




(defun is-ll-1 (grammar)
  (every (compose (curry #'= 2) #'length)
	 (ll-parsing-table grammar)))



