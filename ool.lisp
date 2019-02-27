(defparameter *classes-specs* (make-hash-table))

(defun add-class-spec (name class-spec)
  (setf (gethash name *classes-specs*) class-spec))

(defun get-class-spec (name)
  (gethash name *classes-specs*))

(defun get-class-parents (class)
  (cdr (assoc :parents (get-class-spec class))))

(defun get-class-slot (class)
  (cdr (assoc :slots (get-class-spec class))))

;;; True if class-name is in the hash-table *classes-specs*
;;  If true, class-name is a valid class

(defun classp (class-name)
  (if (get-class-spec class-name)
      t
      nil))

;;; True if every parent is in the hash-table *classes-specs*
;; empty list (no parents) returns true

(defun parentsp (parents)
  (if (and (listp parents) 
	   (or (null parents)
	       (every #'get-class-spec parents)))
      t
      nil))

;;; Deterministic union where 
;;  elements shared are always taken from A
;;  (B - A) + A.
;;  http://clhs.lisp.se/Body/f_unionc.htm
;;  (union '((x 5) (y 6)) '((z 2) (x 4)) :key #'car)
;;  =>  ((X 5) (Y 6) (Z 2))
;;  OR=>  ((X 4) (Y 6) (Z 2))

(defun union-det (a b &key (key #'first) (test #'equal))
  (let ((b-a (set-difference b a :key key :test test)))
    (union b-a a :key key :test test)))

;;; delete this
(defun inherit-slots (acc-slots parents)
  (if (null parents)
      (values acc-slots)
      (let ((inh (get-class-slot (car parents))))
	(inherit-slots (union-det acc-slots inh) (cdr parents)))))

;;; Return a list of all default defined slots for 'class'

(defun slot-inheritance (class)
  ;; add class to the top of superclasses
  ;; so class' slots are taken first
  (let ((class-ordered (cons class (superclass class))))
    (remove-duplicates
     ;; slot accumulation
     (reduce #'append (mapcar #'get-class-slot class-ordered))
     :key #'first :test #'equal :from-end t)))


(defun superclasses--h (parents)
  (if (null parents)
      nil
      (append (superclasses--h (cdr parents))
	      (superclass--h (car parents)))))

(defun superclass--h (parent)
  (let ((grand-parent (get-class-parents parent)))
    (if (null grand-parent)
	(list parent)
	(cons parent (superclasses--h grand-parent)))))

;;; Returns an ordered list of 'class' superclasses

(defun superclass (class)
  ;; The list is reversed last for efficiency
  ;; (cons vs append) in superclass--h
  (reverse
   (remove-duplicates
    (superclasses--h (get-class-parents class)))))



;;; Creates cons pairs (slot-name . slot-value)
;;  from a list of slots
;;  Accumulate the pairs in 'alist'

(defun pair-slots (slots alist)
  (if (null slots)
      (values alist)
      (pair-slots (cddr slots)
		  (acons (first slots)
			 (second slots)
			 alist))))

;;; rewrites method-spec as lambda function
;;; adds "this" as first argument
;;; lambda body contains every form in method-spec

(defun rewrite-method-code (method-spec)
  `(lambda ,(cons 'this (second method-spec))
     ,(cons 'progn (cddr method-spec))))


;;; Associate method-name with following lambda function
;;  last line changes method-spec

(defun process-method (method-name method-spec)
  (setf (fdefinition method-name)
	;;'this' is required to simulate a call on an object
	;;so (method instance) == instance.method
	(lambda (this &rest args)
	  (let ((method-instance (getv this method-name)))
	    (if method-instance ;if getv returned nil throw error
		(apply method-instance this args)
		(error "Error: no method or slot named ~a found ~%"
		       method-name)))))
  (eval (rewrite-method-code method-spec)))

;;; Call process-method if slot is a method

(defun process-slots (slots)
  (mapcar (lambda (slot)
	    (if (and (consp (cdr slot))
		     (eq '=> (cadr slot)))
		(cons (car slot) (process-method (car slot) (cdr slot)))
		slot))
	  slots))

;;; Association list to represent a class

(defun create-class-spec (class-name parents slots)
  (pairlis '(:class :parents :slots)
	   `(,class-name ,parents ,slots)))

;;; Association list to represent an object

(defun create-instance-spec (class-name slots)
  (pairlis '(:class :slots)
	   `(,class-name ,slots)))

;;; Verify the parameters are valid
;;  Create the appropriate assoc list
;;  Add the list to the table

(defun def-class (class-name parents &rest slot-value)
  (if (and
       (symbolp class-name)
       (not (classp class-name)) ; class-name can't be an already valid class
       (parentsp parents)
       (evenp (list-length slot-value))) ; must be pairs (0 is valid)
      (let ((class-spec (create-class-spec
			 class-name
			 parents
			 (pair-slots slot-value '()))))
	(add-class-spec class-name class-spec)
	(values class-name))
      (error "Couldn't create class")))

;;; Inherit all slots from superclasses
;;  Integrate slots redefinition
;;  Make method slots callable

(defun new (class-name &rest slot-value)
  (if (classp class-name)
      (let* ((slot-args (pair-slots slot-value '())) ; slots redefined in new
	     ;;All valid slots for class
	     (all-slots (slot-inheritance class-name)))
	;; A - B = null if all slots of A are in B
	;; no new slots can be defined
	(if (null (set-difference
		   slot-args all-slots :key #'first :test #'equal))
	    (let* ((slot-instance (union-det slot-args all-slots))
		   (processed-slots (process-slots slot-instance)))
	      (values (create-instance-spec
		       class-name
		       processed-slots)))
	    (error "Error: Invalid slot/s specified")))
      (error "Error: Cannot instance object")))

;;;getter
(defun getv (instance slot-name)
  ;; if instance is passed as symbol, evals it
  (let ((instance (if (symbolp instance)
		      (eval instance)
		      instance)))
    ;; instance is an assoc list
    (if (and (listp instance)
	     (classp (cdr (assoc :class instance))))
	(let* ((slots (cdr (assoc :slots instance)))
	       (value (cdr (assoc slot-name slots))))
	  ;; might be a problem if the real value of a slot is nil
	  (if (or (null slots) (null value))
	      (error "Error: Invalid slot")
	      value))
	(error "Error: Invalid instance"))))

;;;recursive getter
;;;every slot except the last must return a valid instance
(defun getvx (instance slot-name &rest other-slots)
  (when (null slot-name)
    (error "Slots cannot be nil"))
  (let ((slots (if (listp slot-name); builds a list of slots the first time
		   slot-name
		   (cons slot-name other-slots))))
    (if (equal 1 (length slots))
	(getv instance (car slots))
	(getvx (getv instance (car slots)) (cdr slots)))))
