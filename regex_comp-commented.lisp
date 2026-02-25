;; partial fn application
(defun partial (fn &rest args)
  (lambda (&rest rest-args)
    (apply fn (append args rest-args))))

;; struct defs

(defstruct nfa
  alphabet
  states
  initial-state
  final-states
  transition-table)

(defstruct dfa
  alphabet
  states
  initial-state
  final-states
  transition-table)

(defstruct transition
  state
  whens)

(defstruct when.
  sym
  next-states)

;; get the next states based off the nfa, current state and sym.
;; this is just a deep fetch really.
(defun next-states (nfa current-state sym)
  (ignore-errors
   (when.-next-states
    (find-if (lambda (w) (eq (when.-sym w) sym))
	     (transition-whens (find-if (lambda (tr)
					  (eq (transition-state tr) current-state))
					(nfa-transition-table nfa)))))))
;; given an nfa and a set of states, build the next transition,
;; based off the alphabet and the various states that are entered.
;; account for epsilon closure.
(defun next-transition (nfa states)
  (make-transition
   :state states
   :whens (loop for sym in (nfa-alphabet nfa)
		collect (make-when.
			 :sym sym
			 :next-states (remove-duplicates
				       (loop for state in states
					     appending (epsilon-closure nfa
									(next-states nfa state sym))))))))


;; figure out all the states that will be entered when
;; going to these states, by following epsilons.
(defun epsilon-closure (nfa states)
  ;; follow epsilons from these states by one iteration.
  ;; figure out which of these are new.
  (let ((next-iter (set-difference 
		    (remove-duplicates
		     (loop for state in states
			   appending (next-states nfa state 'epsilon)))
		    states)))
    ;; if none are new, then return the current states,
    ;; otherwise add these and try again with the larger set.
    (if (null next-iter)
	states
	(epsilon-closure nfa (append states next-iter)))))

;; convert an nfa into a dfa
(defun dfa<-nfa (nfa)
  ;; define the helper function that builds the transition table
  (labels ((build-table (current-table unclosed-states)
	     ;; given the next states find the epsilon closure
	     (let ((next-states (epsilon-closure nfa unclosed-states)))
	       ;; if this state of the NFA has been encountered before
	       ;; then the table doesn't need to be extended, so just return it
	       (if (some (lambda (tr)
			   (null (set-exclusive-or next-states (transition-state tr))))
			 current-table)
		   current-table
		   ;; otherwise, build the transitions for this state, add it to the table,
		   ;; use it as the initial value for a fold on this function to extend the table,
		   ;; and fold on the potential states that could be entered based off the alphabet.
		   (reduce #'build-table
			   (mapcar #'when.-next-states
				   (transition-whens (next-transition nfa next-states)))
			   :initial-value (cons (next-transition nfa next-states)
						current-table))))))
    ;; build the dfa to return
    (let ((table (build-table '() (list (nfa-initial-state nfa)))))
      (make-dfa
       :alphabet (nfa-alphabet nfa)
       :states (mapcar #'transition-state table)
       :initial-state (epsilon-closure nfa (list (nfa-initial-state nfa)))
       ;; final states are states that include something in the nfa's final state list.
       :final-states (remove-if-not (partial #'intersection (nfa-final-states nfa))
				    (mapcar #'transition-state table))
       :transition-table table))))

;; this is a utility function that allows us to add
;; new transitions on epsilon to a given state
(defun extend-epsilon (tr new-states)
  (make-transition
   :state (transition-state tr)
   :whens
   ;; go over the edges. If it's epsilon, append the new state.
   ;; otherwise just keep the old one
   (mapcar (lambda (a-when)
	     (if  (eq 'epsilon (when.-sym a-when))
		  (make-when.
		   :sym 'epsilon
		   :next-states (append new-states
					(when.-next-states a-when)))
		  a-when))
	   ;; if the state has any epsilon transitions we can extend those.
	   ;; otherwise, we need to add an empty epsilon transition to extend.
	   (if (some (lambda (a-when) (eq 'epsilon (when.-sym a-when)))
		     (transition-whens tr))
	       (transition-whens tr)
	       (cons (make-when. :sym 'epsilon
				 :next-states '())
		     (transition-whens tr))))))

;; the nfa may not have any transitions at all for final states.
;; this makes encoding the dfa tricky if we're primarily looking at the transition table.
;; lets make an explicit state with no edges for the final states.
(defun add-final-states (nfa)
  (make-nfa
   :alphabet (nfa-alphabet nfa)
   :states (nfa-states nfa)
   :initial-state (nfa-initial-state nfa)
   :final-states (nfa-final-states nfa)
   :transition-table
   ;; go over the final states and if they're not there cons them onto
   ;; the table. Return the table with everything consed onto it and use that.
   (reduce (lambda (table final-state)
	     (if (some (lambda (tr) (eq final-state (transition-state tr)))
		       table)
		 table
		 (cons (make-transition
		       :state final-state
		       :whens '())
		       table)))
	   (nfa-final-states nfa)
	   :initial-value (nfa-transition-table nfa))))

;; this recursively converts a regex into an nfa.
;; regexes are defined in prefix notation, which dramatically simplifies
;; the process of conversion.
(defun nfa<-regex (alphabet regex-form)
  (cond
    ;; this is our base case. If it's a character we make a simple 2
    ;; state nfa that encodes it.
    ((characterp regex-form)
     (let ((s1 (gensym))
	   (s2 (gensym)))
       (make-nfa
	:alphabet alphabet
	:states (list s1 s2)
	:initial-state s1
	:final-states (list s2)
	:transition-table (list (make-transition
				 :state s1
				 :whens (list (make-when.
					       :sym regex-form
					       :next-states (list s2))))))))
    ;; if it's an and-then statement, we need to fold on a procedure that combines
    ;; two nfas and creates one that accepts the language described by the succession of the 2.
    ;; we do this by only using the finals of the 2nd statement,
    ;; and creating epsilon transitions from the states marked as final from the first nfa
    ;; to the initial state of the second nfa.
    ((eq (car regex-form) 'and-then)
     (flet ((then-2 (a b)
	      (make-nfa
	       :alphabet alphabet
	       :states (append (nfa-states a) (nfa-states b))
	       :initial-state (nfa-initial-state a)
	       :final-states (nfa-final-states b)
	       :transition-table
	       ;; merge the 2 transition tables
	       (append
		;; add the epsilon transitions to initial state of 2nd one
		(loop for tr in (nfa-transition-table a)
		      if (member (transition-state tr) (nfa-final-states a))
			collect (extend-epsilon tr (list (nfa-initial-state b)))
		      else
			collect tr)
		(nfa-transition-table b)))))
       ;; and now we recursively convert each argument into an nfa and then fold all of them
       ;; with the then-2.
       (reduce #'then-2 (mapcar (lambda (f) (add-final-states (nfa<-regex alphabet f))) (cdr regex-form)))))
    ;; if its a choice it's pretty easy. We add one new state, s0, which becomes the initial state.
    ;; it points to the initial state of all the other nfas, and the final states are the union
    ;; of all the constituent nfas.
    ((eq (car regex-form) 'choice)
     (let ((s0 (gensym))
	   (nfas (mapcar (lambda (f) (add-final-states (nfa<-regex alphabet f))) (cdr regex-form))))
       (make-nfa
	:alphabet alphabet
	:states (cons s0 (mapcan #'nfa-states nfas))
	:initial-state s0
	:final-states (mapcan #'nfa-final-states nfas)
	:transition-table
	(cons (make-transition
	       :state s0
	       :whens (list (make-when.
			     :sym 'epsilon
			     :next-states (mapcar #'nfa-initial-state nfas))))
	      ;; recursively convert all the arguments to nfas first and then create the
	      ;; combined NFA that captures the disjunction.
	      (mapcan #'nfa-transition-table
		      nfas)))))
    ;; kleene star. We do this one by adding a new state, making it the initial and the final state,
    ;; adding an epsilon from s0 to the old initial state, and then adding epsilons from the final states
    ;; to s0.
    ((eq (car regex-form) 'star)
     (let ((s0 (gensym))
	   ;; convert the argument to an nfa first
	   (nfa (add-final-states (nfa<-regex alphabet (cadr regex-form)))))
       (make-nfa
	:alphabet alphabet
	:states (cons s0 (nfa-states nfa))
	:initial-state s0
	:final-states (list s0)
	:transition-table
	(cons (make-transition		; make s0
	       :state s0
	       :whens (list (make-when.
			     :sym 'epsilon
			     :next-states (list (nfa-initial-state nfa)))))
	      ;; add in the epsilons from the final states to s0
	      (loop for tr in (nfa-transition-table nfa)
		    if (member (transition-state tr) (nfa-final-states nfa))
		      collect (extend-epsilon tr (list s0))
		    else
		      collect tr)))))
	(t (error "unknown type ~a" regex-form))))

;; now that we have a dfa, we're going to create an executable function that implements it.
;; we'll do this by building out the code for a lambda expression as a list, and then evaling it.
;; this allows us to generate highly specialized code. Instead of storing the dfa inside a closure
;; and then consulting it along with each symbol that comes in,
;; we're going to use the dfa to build a tagbody, a block with labels that support goto.
;;
;; this allows the current state of the dfa to be modeled by the current location of the
;; program counter, and means the pointer is already on the next section of code to be run to process
;; the next symbol.
;;
;; since the behavior is all in pre-compiled code, no runtime overhead is incurred in analyzing/interpreting
;; the structure beyond the initial expense of building the lambda. the behavior is hard-coded, allowing
;; full ahead-of-time and optimization by the compiler and runtime optimization by the hardware.
;;
;; This hinges on the behavior of eval, naturally. Luckily, in Common Lisp evaling a form will cause it to be
;; compiled and then executed, not interpreted. Evaling a lambda will thus compile this expression and yield
;; a procedure object, exactly the same as if it had been written and compiled long ago by the programmer.
;; The runtime generated code is indistinguishable.
;;
;; so all we need to do basically is take the dfa, build out a lambda expression that implements it
;; as efficiently as possible, and then eval it.
(defun lambda<-dfa (dfa)
  ;; labels-map stores a hashmap of the states in the dfa to the symbols we'll use as labels for gotos in the
  ;; tagbody.
  (let ((labels-map (loop with result = (make-hash-table :test 'equal)
			  for state in (dfa-states dfa)
			  do (setf (gethash state result) (gensym))
			  finally (return result))))
    (eval
     `(lambda (s)
	;; get it to run faster. We have a manually coded type check so turning safety to 0 is ok.
	(declare (optimize (speed 3) (safety 0)))
	(check-type s simple-base-string)
	(let ((i 0)		; current character index
	      (strlen (length s))
	      (matchp nil))	; do we accept?
	  (tagbody
	     ;; put in an initial goto to the initial state
	     (go ,(gethash (dfa-initial-state dfa) labels-map))
	     ;; expand out the code to the tagbody form.
	     ;; the structure is: label,
	     ;;                   when(eof == string){goto done}
	     ;;                   switch (char) { when alphabet-symbol: goto next-state ...}
	     ;;                   ...
	     ;; (and of course some code in the prog1 that ticks the character index forward,
	     ;;  and another piece of code that flips matchp to true if we're in a final state and
	     ;;  we're at the end of the string.)
	     ,@(apply #'append
		      (mapcar (lambda (state)
				(let ((transition (find-if (lambda (tr)
							     (equal state (transition-state tr)))
							   (dfa-transition-table dfa)))
				      (finalp (member state (dfa-final-states dfa))))
				  `(,(gethash state labels-map) ; the label
				    (when (= i strlen) ; when we're at the end, goto done
				      ;; if its a final state flip matchp to true before going to done
				      ,@(if finalp '((setf matchp t)) nil) 
				      (go done))
				    (let ((ch (aref s i)))
				      (incf i)
				      (case ch
					,@(loop for a-when in (transition-whens transition)
						collect `((,(when.-sym a-when)) ; the sym for the case
							  ;;  the next goto
							  (go ,(gethash (when.-next-states a-when)
									labels-map)))))))))
			      ;; do this for every state in the dfa
			      (dfa-states dfa)))
	   done) 		; when we goto done, do nothing else, just exit the tagbody
	  matchp)))))		; and finally return whether we accepted.





;;; examples:
;;;
;;; (let ((r (lambda<-dfa (dfa<-nfa (nfa<-regex '(#\a #\b #\c #\d)
;;;                                             '(and-then (star (choice #\a #\b))
;;;                                                        #\a
;;;                                                       (star (choice #\a #\b))))))))
;;;   (funcall r "bbbbbbb")) => NIL
;;;
;;; (let ((r (lambda<-dfa (dfa<-nfa (nfa<-regex '(#\a #\b #\c #\d)
;;;                                             '(and-then (star (choice #\a #\b))
;;;                                                        #\a
;;;                                                       (star (choice #\a #\b))))))))
;;;   (funcall r "bbbabbb")) => T
;;;
;;; performance: for small alphabets and strings of 1000 characters, performance seems
;;;   to be hovering at a speed of about 500M characters per second. (Apple M3, 4ghz)

