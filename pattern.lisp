(defclass nfa ()
  ((states
    :initform (make-hash-table)
    :accessor states)
   (initial-states
    :initform '()
    :accessor initial-states)
   (final-states
    :initform '()
    :accessor final-states)))

(defmethod get-initial-states ((n nfa))
  (initial-states n))

(defmethod is-initial-state? ((n nfa) state)
  (member state (initial-states n)))

(defmethod is-final-state? ((n nfa) state)
  (member state (final-states n)))

(defmethod add-initial-state ((n nfa) state)
  (push state (initial-states n)))

(defmethod add-final-state ((n nfa) state)
  (push state (final-states n)))

(defmethod new-state ((n nfa))
  (let ((new-state (gensym)))
    (setf (gethash new-state (states n)) '())
    new-state))

(defmethod add-edge ((n nfa) src dest edge)
  (push (cons edge dest) (gethash src (states n)))
  (values))

(defmethod remove-edge ((n nfa) src dest edge)
  (setf (gethash src (states n)) (delete (cons edge dest) (gethash src (states n)) :test #'equal))
  (values))

(defmethod get-states ((n nfa))
  (loop for k being the hash-keys in (states n) collecting k))

(defmethod get-transitions ((n nfa) state)
  (gethash state (states n)))

(defmethod get-transitions-to ((n nfa) state)
  (loop for s being the hash-keys in (states n)
	appending (loop for transition in (gethash s (states n))
			when (eql state (cdr transition))
			  collect (cons s (car transition)))))

(defmethod remove-state ((n nfa) state)
  (remhash state (states n))
  (when (is-initial-state? n state)
    (setf (initial-states n) (delete state (initial-states n))))
  (when (is-final-state? n state)
    (setf (final-states n) (delete state (final-states n)))))

(defun make-edge (pattern)
  `',pattern)

(defun compile-sequence (n sequence current-state)
  (if (null sequence)
      current-state
      (let ((next (compile-pattern n (car sequence) current-state)))
	(compile-sequence n (cdr sequence) next))))

(defun compile-pattern (n pattern current-state)
  (if (listp pattern)
      (case (car pattern)
	(alternative
	 (let ((a (new-state n))
	       (b (new-state n))
	       (end (new-state n)))
	   (add-edge n current-state a 'eps)
	   (add-edge n current-state b 'eps)
	   (add-edge n (compile-pattern n (second pattern) a) end 'eps)
	   (add-edge n (compile-pattern n (third pattern) b) end 'eps)
	   end))
	(repeated
	 (let* ((start (new-state n))
		(end (new-state n))
		(x (compile-pattern n (second pattern) start)))
	   (add-edge n current-state start 'eps)
	   (add-edge n x start 'eps)
	   (add-edge n x end 'eps)
	   end))
	(any
	 (let ((end (new-state n)))
	   (add-edge n current-state end 'any)
	   end))
	(pattern
	 (error "unsupported"))
	(sequence
	 (compile-sequence n (cdr pattern) current-state))
	(otherwise
	 (let ((start (new-state n))
	       (end (new-state n)))
	   (add-edge n current-state start 'down)
	   (add-edge n (compile-sequence n pattern start) end 'up)
	   end)))
      (let ((next (new-state n)))
	(add-edge n current-state next (make-edge pattern))
	next)))

(defun pattern->nfa (pattern)
  (let* ((n (make-instance 'nfa))
	 (initial (new-state n)))
    (add-initial-state n initial)
    (add-final-state n (compile-pattern n pattern initial))
    n))

(defun partition (predicate list)
  (loop for elem in list
	if (funcall predicate elem)
	  collect elem into true
	else
	  collect elem into false
	finally (return (values true false))))

(defun remove-eps-transitions (n)
  (labels ((rec ()
	     (let ((recurse nil))
	       (dolist (state (get-states n))
		 (let* ((transitions (get-transitions n state))
			(eps-transitions (remove-if-not (lambda (transition) (eql 'eps (car transition))) transitions)))
		   (unless (null eps-transitions)
		     (setf recurse t))
		   (loop for (_ . dest) in eps-transitions
			 do (loop for (e . d) in (remove-duplicates (get-transitions n dest) :test #'equal)
				  do (add-edge n state d e))
			 do (remove-edge n state dest 'eps)
			 when (is-initial-state? n state)
			   do (add-initial-state n dest)
			 when (is-final-state? n dest)
			   do (add-final-state n state))))
	       (when recurse
		 (rec)))))
    (rec))
  n)

(defun remove-unreachable-states (n)
  (labels ((rec ()
	     (let ((recurse nil))
	       (loop for state in (get-states n)
		     when (and (not (is-initial-state? n state))
			       (null (remove-if (lambda (transition) (eql state (cdr transition))) (get-transitions-to n state))))
		       do (progn
			    (remove-state n state)
			    (setf recurse t)))
	       (when recurse
		 (rec)))))
    (rec))
  n)

(defun make-1-initial-state (n)
  (let ((new-initial-state (new-state n))
	(initial-transitions (remove-duplicates
			      (loop for state in (get-initial-states n)
				    appending (get-transitions n state))
			      :test #'equal)))
    (loop for state in (get-initial-states n)
	  do (remove-state n state))
    (loop for transition in initial-transitions
	  do (add-edge n new-initial-state (cdr transition) (car transition)))
    (add-initial-state n new-initial-state)
    n))

(defun simplify-nfa (n)
  (remove-eps-transitions n)
  (make-1-initial-state n)
  (remove-unreachable-states n))

(ql:quickload :cl-dot)

(defmethod cl-dot:graph-object-node ((graph nfa) object)
  (make-instance 'cl-dot:node
		 :attributes `(:label ""
			       :shape ,(cond
					 ((is-final-state? graph object) :doublecircle)
					 ((is-initial-state? graph object) :square)
					 (t :circle)))))

(defmethod cl-dot:graph-object-edges ((graph nfa))
  (loop for state being the hash-keys in (states graph) using (hash-value v)
	appending (mapcar (lambda (x) (list state (cdr x) `(:label ,(format nil "~a" (car x))))) v)))

(defmethod draw-nfa ((n nfa))
  (let ((cl-dot:*dot-path* "/usr/local/bin/dot"))
    (uiop:with-temporary-file (:pathname pathname :type "pdf")
      (cl-dot:dot-graph (cl-dot:generate-graph-from-roots n '() '(:rankdir "LR")) pathname :format :pdf)
      (uiop:run-program `("open" ,(namestring pathname))))))
