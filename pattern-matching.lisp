(defpackage :pattern-matching
  (:use :cl)
  (:import-from :alexandria :appendf :when-let :if-let :set-equal))

(in-package :pattern-matching)

;;; NFA implementation

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

;;; Pattern -> NFA

(defun remove-nil-vals (plist)
  (loop for (key val) on plist by #'cddr
	when val
	  appending (list key val)))

(defun make-edge (name &rest plist)
  (cons name (remove-nil-vals plist)))

(defun compile-sequence (n sequence current-state &optional &key (orderless nil))
  (reduce
   (lambda (state subpattern)
     (compile-pattern n subpattern state :orderless orderless))
   sequence
   :initial-value current-state))

(defvar *orderless-symbols* '(+ *))

(defun is-orderless? (symbol)
  (if (member symbol *orderless-symbols*) t nil))

(defun compile-orderless (n pattern current-state)
  (let ((new-state (new-state n)))
    (add-edge n current-state new-state (make-edge :constant :value (car pattern)))
    (compile-sequence n (cdr pattern) new-state :orderless t)))

(defconstant eps-edge (make-edge :eps))

(defun compile-pattern (n pattern current-state &optional &key (orderless nil))
  (if (listp pattern)
      (case (car pattern)
	(alternative
	 (let ((a (new-state n))
	       (b (new-state n))
	       (end (new-state n)))
	   (add-edge n current-state a eps-edge)
	   (add-edge n current-state b eps-edge)
	   (add-edge n (compile-pattern n (second pattern) a :orderless orderless) end eps-edge)
	   (add-edge n (compile-pattern n (third pattern) b :orderless orderless) end eps-edge)
	   end))
	(repeated
	 (let* ((start (new-state n))
		(end (new-state n))
		(x (compile-pattern n (second pattern) start :orderless orderless)))
	   (add-edge n current-state start eps-edge)
	   (add-edge n x start eps-edge)
	   (add-edge n x end eps-edge)
	   end))
	(any
	 (let ((end (new-state n)))
	   (add-edge n current-state end (make-edge :any :orderless orderless))
	   end))
	(pattern
	 (let ((start (new-state n))
	       (end (new-state n)))
	   (add-edge n current-state start (make-edge :start-var :var (second pattern) :orderless orderless))
	   (add-edge n (compile-pattern n (third pattern) start :orderless orderless) end (make-edge :end-var :var (second pattern) :orderless orderless))
	   end))
	(patternsequence
	 (compile-sequence n (cdr pattern) current-state :orderless orderless))
	(otherwise
	 (let ((start (new-state n))
	       (end (new-state n)))
	   (add-edge n current-state start (make-edge :down :orderless orderless))
	   (let ((pattern-orderless? (and (not (null pattern)) (is-orderless? (car pattern)))))
	     (add-edge
	      n
	      (cond
		(pattern-orderless? (compile-orderless n pattern start))
		(t (compile-sequence n pattern start)))
	      end
	      (make-edge :up :orderless pattern-orderless?)))
	   end)))
      (let ((next (new-state n)))
	(add-edge n current-state next (make-edge :constant :value pattern :orderless orderless))
	next)))

(defun pattern->nfa (pattern)
  (let* ((n (make-instance 'nfa))
	 (initial (new-state n)))
    (add-initial-state n initial)
    (add-final-state n (compile-pattern n pattern initial))
    n))

;;; Optimize/simplify NFAs
;;; TODO: combine equivalent states

(defun remove-eps-transitions (n)
  (labels ((rec ()
	     (let ((recurse nil))
	       (dolist (state (get-states n))
		 (let* ((transitions (get-transitions n state))
			(eps-transitions (remove-if-not (lambda (transition) (eql :eps (caar transition))) transitions)))
		   (unless (null eps-transitions)
		     (setf recurse t))
		   (loop for (edge . dest) in eps-transitions
			 do (loop for (e . d) in (remove-duplicates (get-transitions n dest) :test #'equal)
				  do (add-edge n state d e))
			 do (remove-edge n state dest edge)
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

;;; Match NFA

(defstruct matching-state
  (indices '())
  (var-starts '())
  (captures '())
  (orderless-visited '()))

(defun deep-copy-matching-state (matching-state)
  (let ((copy (copy-matching-state matching-state)))
    (setf (matching-state-indices copy) (copy-list (matching-state-indices copy)))
    (setf (matching-state-var-starts copy) (copy-alist (matching-state-var-starts copy)))
    (setf (matching-state-captures copy) (copy-alist (matching-state-captures copy)))
    (setf (matching-state-orderless-visited copy) (copy-alist (matching-state-orderless-visited copy)))
    copy))

(defun incf-last-index (matching-state)
  (unless (null (matching-state-indices matching-state))
    (incf (car (last (matching-state-indices matching-state))))))

(defun index-expression (expression indices)
  (if (null indices)
      (values expression t)
      (if (or (not (listp expression)) (>= (car indices) (length expression)))
	  (values nil nil)
	  (index-expression (elt expression (car indices)) (cdr indices)))))

(defun get-capture (expression matching-state var orderless?)
  (if-let (start (cdr (assoc var (matching-state-var-starts matching-state))))
    (let* ((up-level (index-expression expression (butlast (matching-state-indices matching-state))))
	   (sequence (if orderless?
			 (mapcar (lambda (i) (elt up-level i)) (subseq (get-orderless-visited matching-state) start))
			 (subseq up-level start (car (last (matching-state-indices matching-state))))))
	   (capture (if (= 1 (length sequence))
			(car sequence)
			`(sequence ,@sequence))))
      capture)
    ;; start is nil -> capture whole expression
    expression))

(defun get-orderless-visited (matching-state)
  (let ((depth (1- (length (matching-state-indices matching-state)))))
    (if-let (visited (cdr (assoc depth (matching-state-orderless-visited matching-state))))
      visited
      (let ((visited '()))
	(push (cons depth visited) (matching-state-orderless-visited matching-state))
	visited))))

(defun add-visited-index (matching-state index)
  (let ((depth (1- (length (matching-state-indices matching-state)))))
    (appendf (cdr (assoc depth (matching-state-orderless-visited matching-state))) (list index))))

(defun match-rec (nfa state expression matching-state found)
  (macrolet ((try ((new-matching-state) &body body)
	       `(let ((,new-matching-state (deep-copy-matching-state matching-state)))
		  (multiple-value-bind (res matched)
		      (match-rec nfa (progn ,@body) expression ,new-matching-state found)
		    (when matched
		      (funcall found res)))))
	     (try-orderless-possibilities ((new-matching-state index) predicate &body body)
	       `(let ((list (cdr (index-expression expression (butlast (matching-state-indices matching-state)))))
		      (visited (get-orderless-visited matching-state)))
		  (loop for elem in list and ,index from 1
			when (and (not (member ,index visited)) (funcall ,predicate elem))
			  do (multiple-value-bind (res matched)
				 (let ((,new-matching-state (deep-copy-matching-state matching-state)))
				   (match-rec nfa (progn ,@body) expression ,new-matching-state found))
			       (when matched
				 (funcall found res)))))))
    (multiple-value-bind (subexpression in-bounds?)
	(index-expression expression (matching-state-indices matching-state))
      (dolist (transition (get-transitions nfa state)
			  (values (matching-state-captures matching-state) (if (is-final-state? nfa state) t nil)))
	(let* ((edge (caar transition))
	       (plist (cdar transition))
	       (dest (cdr transition))
	       (orderless? (getf plist :orderless)))
	  (case edge
	    (:down
	     (if orderless?
		 (try-orderless-possibilities (new-matching-state i)
					      #'listp
					      (add-visited-index new-matching-state i)
					      (setf (car (last (matching-state-indices new-matching-state))) i)
					      (appendf (matching-state-indices new-matching-state) '(0))
					      dest)
		 (when (and in-bounds? (listp subexpression))
		   (try (new-matching-state)
			(appendf (matching-state-indices new-matching-state) '(0))
			dest))))
	    (:up
	     (when (= (length (index-expression expression (butlast (matching-state-indices matching-state))))
		      (if orderless?
			  (1+ (length (get-orderless-visited matching-state)))
			  (car (last (matching-state-indices matching-state)))))
	       (try (new-matching-state)
		    (setf (matching-state-indices new-matching-state) (butlast (matching-state-indices new-matching-state)))
		    (incf-last-index new-matching-state)
		    dest)))
	    (:any
	     (if orderless?
		 (try-orderless-possibilities (new-matching-state i)
					      (lambda (_) (declare (ignore _)) t)
					      (add-visited-index new-matching-state i)
					      dest)
		 (when in-bounds?
		   (try (new-matching-state)
			(incf-last-index new-matching-state)
			dest))))
	    (:constant
	     (let ((value (getf plist :value)))
	       (if orderless?
		   (try-orderless-possibilities (new-matching-state i)
						(lambda (x) (equal x value))
						(add-visited-index new-matching-state i)
						dest)
		   (when (equal subexpression value)
		     (try (new-matching-state)
			  (incf-last-index new-matching-state)
			  dest)))))
	    (:start-var
	     (let ((var (getf plist :var)))
	       (try (new-matching-state)
		    (push (cons var
				(if orderless?
				    (length (get-orderless-visited new-matching-state))
				    (car (last (matching-state-indices new-matching-state)))))
			  (matching-state-var-starts new-matching-state))
		    dest)))
	    (:end-var
	     (let* ((var (getf plist :var))
		    (capture (get-capture expression matching-state var orderless?)))
	       (if (member var (matching-state-captures matching-state) :key #'car)
		   (when (equal capture (cdr (assoc var (matching-state-captures matching-state))))
		     (try (_) dest))
		   (try (new-matching-state)
			(push (cons var capture) (matching-state-captures new-matching-state))
			dest))))))))))

(defun match (nfa expression found)
  (loop for state in (get-initial-states nfa)
	do (match-rec nfa state expression (make-matching-state) found)))

(defun first-match (nfa expression)
  (match nfa expression (lambda (res) (return-from first-match (values res t))))
  (values nil nil))

(defun all-matches (nfa expression)
  (let ((results '()))
    (match nfa expression (lambda (res) (push res results)))
    (if (null results)
	(values nil nil)
	(values (nreverse results) t))))

;;; Testing

(defun captures-equal (a b)
  (set-equal a b :test #'equal))

(defun all-captures-equal (a b)
  (set-equal a b :test #'captures-equal))

(defmacro test-pattern (pattern &body test-forms)
  `(let ((nfa (simplify-nfa (pattern->nfa ',pattern))))
     ,@(loop for (kind expression expected) in test-forms
	     collecting (case kind
			  (:matches `(multiple-value-bind (captures matches?) (first-match nfa ',expression)
				       (assert (and matches? (captures-equal captures ',expected)))))
			  (:rejects `(multiple-value-bind (captures matches?) (first-match nfa ',expression)
				       (declare (ignore captures))
				       (assert (not matches?))))
			  (:matches-all `(multiple-value-bind (all-captures matches?) (all-matches nfa ',expression)
					   (assert (and matches? (all-captures-equal all-captures ',expected)))))))))

(defun test-matching ()
  (test-pattern (f (pattern x (any)))
    (:matches (f y) ((x . y)))
    (:matches (f (g 1 2 3)) ((x . (g 1 2 3))))
    (:rejects (g y)))
  (test-pattern (pattern x (alternative a b))
    (:matches a ((x . a)))
    (:matches b ((x . b)))
    (:rejects 1))
  (test-pattern (+ (pattern x (repeated a)) b c)
    (:matches (+ c a b a) ((x . (sequence a a))))
    (:rejects (+ b c))
    (:rejects (+ a a b)))
  (test-pattern (+ 1 2 3)
    (:matches (+ 3 2 1))
    (:rejects (+ 1 2 3 4)))
  (test-pattern (g (pattern x (any)) (pattern y (any)) (pattern z (any)))
    (:matches (g 1 2 3) ((z . 3) (y . 2) (x . 1)))
    (:rejects (g 1 2 3 4)))
  (test-pattern (+ (pattern x (patternsequence 1 (any) 3)) a (pattern x (repeated (any))))
    (:matches (+ 1 1 2 a 2 3 3) ((x . (sequence 1 2 3))))
    (:rejects (+ 1 1 2 a 4 3 3))
    (:rejects (+ 1 2 3 1 2 3))
    (:rejects (+ 1 2 a 2 3 3)))
  (test-pattern (+ 1 (+ a b) 3)
    (:matches (+ (+ b a) 3 1)))
  (test-pattern (pattern x (f (repeated (any))))
    (:matches (f 1 2 3) ((x . (f 1 2 3))))
    (:rejects (f)))
  (test-pattern (+ (pattern x (any)) (pattern y (any)))
    (:matches-all (+ a b) (((x . a) (y . b)) ((x . b) (y . a))))))

;;; Plot NFAs

(defmethod cl-dot:graph-object-node ((graph nfa) object)
  (make-instance 'cl-dot:node
		 :attributes `(:label ""
			       :shape ,(cond
					 ((is-final-state? graph object) :doublecircle)
					 ((is-initial-state? graph object) :square)
					 (t :circle)))))

(defmethod cl-dot:graph-object-edges ((graph nfa))
  (loop for state being the hash-keys in (states graph) using (hash-value v)
	appending (mapcar (lambda (x) (list state (cdr x) `(:label ,(format nil "~{~s~^ ~}" (car x))))) v)))

(defmethod draw-nfa ((n nfa))
  (let ((cl-dot:*dot-path* "/usr/local/bin/dot"))
    (uiop:with-temporary-file (:pathname pathname :type "pdf")
      (cl-dot:dot-graph (cl-dot:generate-graph-from-roots n '() '(:rankdir "LR")) pathname :format :pdf)
      (uiop:run-program `("open" ,(namestring pathname))))))
