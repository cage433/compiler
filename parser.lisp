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

(defun join-and-trunc (exps k)
  (foldl [on-all-pairs {[trunc k] append}]
		 '(nil)
		 exps))

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
		  do (f-k-add-all X (join-and-trunc (mapcar #'f-k-get Y-s) k))))
	  f-k)))



;; Follows algorithm for 1 element -
;; For each production X -> Y_1 ... Y_n
;; For 1 <= i <= n, if Y_i+1, ..., Y_n are all nullable then
;; follows(Y_i) contains follows(X)
;; for each j, i < j <= n,
;;    if Y_i+1, ..., Y_j-1 are all nullable then
;;  	follows(Y_i) contains first(Y_j)




(defun unique-elements (list &key (test #'equal))
  (labels ((recurse (list acc)
					(cond ((null list) acc)
						  ((member (car list) acc :test test) (recurse (cdr list) acc))
						  (t (recurse (cdr list) (cons (car list) acc))))))
	(recurse list '())))
(defun join-expressions (exps-1 exps-2 k)
  (unique-elements
	(mapcar [trunc k]
	  (mapcan (lambda (x) (mapcar 
							(lambda (y) (append x y)) 
							exps-2)) 
			  exps-1))))
(defun exp-firsts-k (exp firsts-k k)
  (with-multi-map firsts-k
	(labels ((recurse (exp acc)
					  (format t "Acc = ~a~%" acc)
					  (format t "Exp on ~a are ~a~%" (car exp) (firsts-k-get (car exp)))
					  (if (null exp)
						acc
						(recurse (cdr exp) 
								 (join-expressions 
								   acc 
								   (firsts-k-get (car exp)) 
								   k)))))
			 (recurse exp (list nil)))))

;;
;; Better algorithm for k elements
;; For each production X -> Y_1 ... Y_n
;; For 1 <= i <= n - 1
;; Follows(Y_i, k) contains firsts (Y_i+1, ..., Y_n, k) + Follows(X, k) truncated to k
;; Follows(X, k) contains Follows(Y_n, k)

;; (defun follows-k (grammar k)
;;   (let ((foll-k (make-list-multi-map))
;; 		(firsts-k (firsts-k grammar k))
;; 		(saved-size))
;; 	(with-multi-map foll-k
;; 		(until (eq saved-size foll-k-size)
;; 		  (setq saved-size foll-k-size)
;; 		  (loop for (X . Y-s) in grammar
;; 			do (mapl (dbind-lambda (Y-i . Y-i+) 
;; 								   (foll-k-add-all Y-i 
;; 												   (exp-firsts-k Y-i+ firsts-k k)
;; 												   (join-and-trunc (append (mapcar #'firsts-k-get Y-i+) 
;; 																		   (foll-k-get X)) 
;; 																   k)))
;; 					 Y-s)))
;; 		(foll-k-map))))
		  	

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



