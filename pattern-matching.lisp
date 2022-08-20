(defpackage :pattern-matching
  (:use :cl)
  (:import-from :alexandria :if-let :set-equal))

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

(defun compile-sequence (n sequence current-state &optional &key (orderless nil) (flat nil) (one-identity nil))
  (reduce
   (lambda (state subpattern)
     (compile-pattern n subpattern state :orderless orderless :flat flat :one-identity one-identity))
   sequence
   :initial-value current-state))

(defvar *symbol-attributes*
  '((+ . (orderless flat one-identity))
    (* . (orderless flat one-identity))
    (dot . (flat one-identity))))

(defun has-attribute? (symbol attribute)
  (if (member attribute (cdr (assoc symbol *symbol-attributes*))) t nil))

(defconstant eps-edge (make-edge :eps))

(defun compile-pattern (n pattern current-state &optional &key (orderless nil) (flat nil) (one-identity nil))
  (if (listp pattern)
      (case (car pattern)
	(alternative
	 (let ((a (new-state n))
	       (b (new-state n))
	       (end (new-state n)))
	   (add-edge n current-state a eps-edge)
	   (add-edge n current-state b eps-edge)
	   (add-edge n (compile-pattern n (second pattern) a :orderless orderless :flat flat :one-identity one-identity) end eps-edge)
	   (add-edge n (compile-pattern n (third pattern) b :orderless orderless :flat flat :one-identity one-identity) end eps-edge)
	   end))
	(repeated
	 (let* ((start (new-state n))
		(end (new-state n))
		(x (compile-pattern n (second pattern) start :orderless orderless :flat flat :one-identity one-identity)))
	   (add-edge n current-state start eps-edge)
	   (add-edge n x start eps-edge)
	   (add-edge n x end eps-edge)
	   end))
	(blank
	 (if flat
	     (let ((start (new-state n))
		   (end (new-state n))
		   (end2 (new-state n)))
	       ;; flat (repeated (blank))
	       (add-edge n current-state start (make-edge :start-flat))
	       (add-edge n start end (make-edge :blank :orderless orderless))
	       (when one-identity
		 (let ((end1 (new-state n)))
		   (add-edge n end end1 (make-edge :blank :orderless orderless))
		   (setf end end1)))
	       (add-edge n end end (make-edge :blank :orderless orderless))
	       (add-edge n end end2 (make-edge :end-flat))
	       ;; or (blank)
	       (add-edge n current-state end2 (make-edge :blank :orderless orderless))
	       end2)
	     (let ((end (new-state n)))
	       (add-edge n current-state end (make-edge :blank :orderless orderless))
	       end)))
	(pattern
	 (let ((start (new-state n))
	       (end (new-state n)))
	   (add-edge n current-state start (make-edge :start-var :var (second pattern) :orderless orderless))
	   (add-edge n (compile-pattern n (third pattern) start :orderless orderless :flat flat :one-identity one-identity) end (make-edge :end-var :var (second pattern) :orderless orderless))
	   end))
	(patternsequence
	 (compile-sequence n (cdr pattern) current-state :orderless orderless :flat flat :one-identity one-identity))
	(otherwise
	 (let ((start (new-state n))
	       (end (new-state n)))
	   (add-edge n current-state start (make-edge :down :orderless orderless :head (car pattern)))
	   (let ((pattern-orderless? (has-attribute? (car pattern) 'orderless))
		 (pattern-flat? (has-attribute? (car pattern) 'flat))
		 (pattern-one-identity? (has-attribute? (car pattern) 'one-identity)))
	     (add-edge n
	      (compile-sequence n (cdr pattern) start :orderless pattern-orderless? :flat pattern-flat? :one-identity pattern-one-identity?)
	      end
	      (make-edge :up)))
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
  expression
  (visited-indices '())
  (var-starts '())
  (flat-ranges '()))

(defun visit-index (matching-state index)
  (let ((new-matching-state (copy-matching-state matching-state)))
    (setf (matching-state-visited-indices new-matching-state)
	  (cons index (copy-list (matching-state-visited-indices new-matching-state))))
    new-matching-state))

(defun add-var-start (matching-state var)
  (let ((new-matching-state (copy-matching-state matching-state)))
    (setf (matching-state-var-starts new-matching-state)
	  (cons (cons var (length (matching-state-visited-indices new-matching-state)))
		(copy-list (matching-state-var-starts new-matching-state))))
    new-matching-state))

(defun add-flat-range (matching-state)
  (let ((new-matching-state (copy-matching-state matching-state)))
    (setf (matching-state-flat-ranges new-matching-state)
	  (cons (length (matching-state-visited-indices new-matching-state))
		(copy-list (matching-state-flat-ranges new-matching-state))))
    new-matching-state))

(defun last-index (matching-state)
  (car (matching-state-visited-indices matching-state)))

(defun unvisited-indices (matching-state)
  (loop for i from 0 below (length (matching-state-expression matching-state))
	unless (member i (matching-state-visited-indices matching-state))
	  collect i))

(defun get-capture (matching-state var)
  (let* ((start (cdr (assoc var (matching-state-var-starts matching-state))))
	 (indices (nreverse (subseq (matching-state-visited-indices matching-state) 0 (- (length (matching-state-visited-indices matching-state)) start))))
	 (capture-seq (mapcar (lambda (i) (elt (matching-state-expression matching-state) i)) indices))
	 (capture-seq-flats
	   (loop for (e s) on (matching-state-flat-ranges matching-state) by #'cddr
		 for flat-start = (- (length (matching-state-visited-indices matching-state)) e)
		 for flat-end = (- (length (matching-state-visited-indices matching-state)) s)
		 with last = 0
		 when (<= flat-end (length capture-seq))
		   append (subseq capture-seq last flat-start) into r
		   and collect (cons (car (matching-state-expression matching-state)) (subseq capture-seq flat-start flat-end)) into r
		   and do (setf last flat-end)
		 finally
		    (return (append r (subseq capture-seq last)))))
	 (capture (if capture-seq-flats capture-seq-flats capture-seq)))
    (if (= (length capture) 1)
	(car capture)
	`(sequence ,@capture))))

(defun match-rec (nfa state matching-state-stack captures found)
  (macrolet ((do-next ((expression index) &body body)
	       `(dolist (,index (if orderless?
				    (unvisited-indices matching-state)
				    (let ((next-index (1+ (last-index matching-state))))
				      (when (< next-index (length (matching-state-expression matching-state)))
					(list next-index)))))
		  (let ((,expression (elt (matching-state-expression matching-state) ,index)))
		    ,@body))))
    (let ((matching-state (car matching-state-stack)))
      (dolist (transition (get-transitions nfa state))
	(let* ((edge (caar transition))
	       (plist (cdar transition))
	       (dest (cdr transition))
	       (orderless? (getf plist :orderless)))
	  (flet ((consume-next-if (predicate)
		   (do-next (expression index)
		     (when (funcall predicate expression)
		       (let ((new-matching-state (visit-index matching-state index)))
			 (match-rec nfa dest (cons new-matching-state (cdr matching-state-stack)) captures found))))))
	    (ecase edge
	      (:down
	       (let ((head (getf plist :head)))
		 (do-next (expression index)
		   (when (and (listp expression) (eql head (car expression)))
		     (let ((new-matching-state (make-matching-state :expression expression :visited-indices '(0))))
		       (match-rec nfa dest (cons new-matching-state (cons (visit-index matching-state index) (cdr matching-state-stack))) captures found))))))
	      (:up
	       (when (= (length (matching-state-expression matching-state)) (length (matching-state-visited-indices matching-state)))
		 (match-rec nfa dest (cdr matching-state-stack) captures found)))
	      (:blank
	       (consume-next-if (lambda (_) (declare (ignore _)) t)))
	      (:constant
	       (let ((value (getf plist :value)))
		 (consume-next-if (lambda (x) (equal value x)))))
	      (:start-var
	       (let* ((var (getf plist :var))
		      (new-matching-state (add-var-start matching-state var)))
		 (match-rec nfa dest (cons new-matching-state (cdr matching-state-stack)) captures found)))
	      (:end-var
	       (let* ((var (getf plist :var))
		      (capture (get-capture matching-state var)))
		 (if-let (old-capture (cdr (assoc var captures)))
		   (when (equal capture old-capture)
		     (match-rec nfa dest matching-state-stack captures found))
		   (match-rec nfa dest matching-state-stack (cons (cons var capture) (copy-alist captures)) found))))
	      (:start-flat
	       (match-rec nfa dest (cons (add-flat-range matching-state) (cdr matching-state-stack)) captures found))
	      (:end-flat
	       (match-rec nfa dest (cons (add-flat-range matching-state) (cdr matching-state-stack)) captures found))))))
      (when (is-final-state? nfa state)
	(funcall found captures)))))

(defun match (nfa expression found)
  (loop for state in (get-initial-states nfa)
	do (match-rec nfa state (list (make-matching-state :expression (list nil expression) :visited-indices '(0))) '() found)))

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
  (test-pattern (f (pattern x (blank)))
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
  (test-pattern (g (pattern x (blank)) (pattern y (blank)) (pattern z (blank)))
    (:matches (g 1 2 3) ((z . 3) (y . 2) (x . 1)))
    (:rejects (g 1 2 3 4)))
  (test-pattern (+ (pattern x (patternsequence 1 (blank) 3)) a (pattern x (repeated (blank))))
    (:matches (+ 1 1 2 a 2 3 3) ((x . (sequence 1 2 3))))
    (:rejects (+ 1 1 2 a 4 3 3))
    (:rejects (+ 1 2 3 1 2 3))
    (:rejects (+ 1 2 a 2 3 3)))
  (test-pattern (+ 1 (+ a b) 3)
    (:matches (+ (+ b a) 3 1)))
  (test-pattern (pattern x (f (repeated (blank))))
    (:matches (f 1 2 3) ((x . (f 1 2 3))))
    (:rejects (f)))
  (test-pattern (+ (pattern x (blank)) (pattern y (blank)))
    (:matches-all (+ a b) (((x . a) (y . b)) ((x . b) (y . a)))))
  (test-pattern (f (pattern x (patternsequence 1 (pattern y (patternsequence 2 3)) 4)))
    (:matches (f 1 2 3 4) ((x . (sequence 1 2 3 4)) (y . (sequence 2 3)))))
  (test-pattern (dot a (pattern x (blank)))
    (:matches (dot a b c) ((x . (dot b c)))))
  (test-pattern (dot (pattern x (patternsequence a (blank) d)))
    (:matches (dot a b d) ((x . (sequence a b d))))
    (:matches (dot a b c d) ((x . (sequence a (dot b c) d)))))
  (test-pattern (dot (blank) (pattern x (blank)) (blank))
    (:matches (dot a b c) ((x . b)))
    (:matches-all (dot a b c d) (((x . b)) ((x . (dot b c))) ((x . c))))))

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
