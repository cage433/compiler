
(defmacro! make-list-map (&key (key-test #'equal) (value-test #'equal))
  `(let ((,g!this) (map '()))
	 (setq ,g!this
		   (dlambda
			 (:put (key value) 
				   (if (f ,value-test value (f ,g!this :get key))
					 nil
					 (progn
					   (f ,g!this :remove key)
					   (push (cons key value) map)
					   t)))
			 (:get (key) (aif (assoc key map :test ,key-test)
							  (values (cdr it) t)
							  (values nil nil)))
			 (:remove (key) (setq map (remove-if (c ,key-test key) map :key #'car)))
			 (:contains (key) (assoc key map :test ,key-test))
			 (:values () (mapcar #'cdr map))
			 (:keys () (mapcar #'car map))
			 (:size () (length map))
			 (:map () map)
			 ))
	 	
	 ,g!this))

(defmacro! make-list-multi-map (&key (key-test #'equal) (value-test #'equal))
  `(let ((,g!this) (map (make-list-map :key-test ,key-test)))
	 (setq ,g!this
		   (dlambda
			 (:add (key value) 
				   (if (member value (f map :get key) :test ,value-test)
					 nil
					 (f map :put key (cons value (f map :get key)))))
			 (:add-all (key values) (loop for v in values do (f ,g!this :add key v)))
			 (:get (key) (f map :get key))
			 (:remove-all (key) (f map :remove key))
			 (:remove (key value) (f map :put key (remove value (f map :get key) :test ,value-test)))
			 (:values-size () (apply #'+ (mapcar #'length (f map :values))))
			 (:keys-size () (f map :size))
			 (:size () (+ (f ,g!this :keys-size) (f ,g!this :values-size)))
			 (:map () (f map :map))
			 ))
	 ,g!this))

(define-test test-list-map
  (let ((map (make-list-map)))
	(assert-equal 0 (f map :size))
	(f map :put 1 17)
	(assert-equal 1 (f map :size))
	(assert-equal 17 (f map :get 1))
	(assert-true (f map :contains 1))
	(assert-false (f map :contains 0))
	(f map :put "foo" "bar")
	(assert-equal 2 (f map :size))
	(assert-equal 2 (length (intersection (list 1 "foo") (f map :keys) :test #'equal)))
	(assert-equal 2 (length (intersection (list 17 "bar") (f map :values) :test #'equal)))
	(f map :remove 1)
	(assert-equal 1 (f map :size))
	(f map :remove "foo")
	(assert-equal 0 (f map :size))
	))


(define-test test-list-multi-map
  (let ((map (make-list-multi-map)))
	(assert-equal 0 (f map :keys-size))
	(assert-equal 0 (f map :values-size))
	(assert-false (f map :contains 33))
	(f map :add 33 100)
	(f map :add 33 55)
	(assert-equal 1 (f map :keys-size))
	(assert-equal 2 (f map :values-size))
	(assert-true (member 100 (f map :get 33)))
	(f map :remove 33 100)
	(assert-false (member 100 (f map :get 33)))
	(assert-true (member 55 (f map :get 33)))
	(assert-equal '(55) (f map :get 33))
	(f map :add "foo" 123)
	(f map :add "foo" 123)
	(f map :add "foo" 444)
	(assert-equal 2 (f map :keys-size))
	(assert-equal 3 (f map :values-size))
	(f map :add-all "foo" (list 99 100))
	(assert-equal 2 (f map :keys-size))
	(assert-equal 5 (f map :values-size))
	))
(run-tests test-list-map)
(run-tests test-list-multi-map)


;; Saved as this is one of my first uses of nested backquotes. It works,
;; but turned out to be more useful to have these as functions rather than
;; macros. Needed to pass them to map.
(defmacro! with-multi-map (map &body body)
  (dbind (size-sym get-sym add-sym add-all-sym map-sym) (mapcar #_(symb map _) '(-size -get -add -add-all -map))
		 `(macrolet ((,get-sym (,g!key) `(f ,',map :get ,,g!key))
					 (,add-sym (,g!key ,g!value) `(f ,',map :add ,,g!key ,,g!value))
					 (,add-all-sym (,g!key ,g!values) `(f ,',map :add-all ,,g!key ,,g!values))
					 (,map-sym () `(f ,',map :map)))
			(symbol-macrolet ((,size-sym (f ,map :size)))
							 ,@body))))

