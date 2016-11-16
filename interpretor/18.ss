;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss") 

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

(define (literal? var)
  (or (symbol? var)
      (boolean? var)
      (string? var)
      (number? var)
      (vector? var)
      (quoted? var)))

(define (literal-ext? var)
  (or (symbol? var)
      (boolean? var)
      (string? var)
      (number? var)
      (vector? (list 'quote var))
      (list? (list 'quote var))))

(define (expression-or-void? var)
	(or (expression? var)
		(equal? var (void))))

(define (quoted? var)
  (and (list? var)
       (eq? (1st var) 'quote)))

(define (improper? pair)
  (if (and (not (null? pair))
	   (not (eq?   (cdr pair) '()))
	   (not (pair? (cdr pair))))
      #t
      (if (null? (cdr pair))
	  #f
	  (improper? (cdr pair)))))

(define (get-variable pair)
  (if (and (not (null? pair))
	   (not (eq?   (cdr pair) '()))
	   (not (pair? (cdr pair))))
      (cdr pair)
      (if (null? (cdr pair))
	  #f
	  (get-variable (cdr pair)))))

(define (get-fixed pair)
  (if (and (not (null? pair))
	   (not (eq?   (cdr pair) '()))
	   (not (pair? (cdr pair))))
      (cons (car pair) '())
      (if (null? (cdr pair))
	  #f
	  (cons (car pair) (get-fixed (cdr pair))))))

(define exp-has-else
  (lambda (x)
    (ormap (lambda (condition)
	     (equal? (car condition) 'else)) x)))

(define all-but-last
  (lambda (lst)
    (if (<= (length lst) 1)
	'()
	(cons (car lst) (all-but-last (cdr lst))))))

(define last
  (lambda (ls)
    (last-helper ls (car ls))))

(define last-helper
  (lambda (ls ch)
    (if (null? ls)
	ch
	(last-helper (cdr ls) (car ls)))))


;; parsed expression

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lambda-variable-exp
   (var symbol?)
   (bodies (list-of expression?))]
  [lambda-improper-exp
   (vars (list-of symbol?))
   (var symbol?)
   (bodies (list-of expression?))]
  [lambda-fixed-exp
   (vars (list-of symbol?))
   (bodies (list-of expression?))]
  [app-exp
   (rator expression?)
   (rands (list-of expression?))]
  [lit-exp
   (id literal-ext?)] ; Expand to include other variable types
  [if-exp
   (test-exp expression?)
   (then-exp expression?)
   (else-exp expression?)]
  [if-onlythen-exp
   (test-exp expression?)
   (then-exp expression?)]
  [let-exp
   (vars (list-of symbol?))
   (exps (list-of expression?))
   (bodies (list-of expression?))]
  [let*-exp
   (vars (list-of symbol?))
   (exps (list-of expression?))
   (bodies (list-of expression?))]
  [letrec-exp
   (proc-names (list-of symbol?))
   (fixed-idss (list-of (list-of symbol?)))
   (variable-idss (list-of (list-of symbol?)))
   (bodiess (list-of (list-of expression?)))
   (letrec-bodies (list-of expression?))]
  [namedlet-exp
   (id symbol?)
   (vars (list-of symbol?))
   (exps (list-of expression?))
   (bodies (list-of expression?))]
  [set!-exp
   (id symbol?)
   (set-exp expression?)]
  [cond-exp
   (conditions (list-of expression?))
   (exps (list-of expression?))
   (else-exp expression?)]
  [cond-no-else-exp
   (conditions (list-of expression?))
   (exps (list-of expression?))]
  [and-exp
   (args (list-of expression?))]
  [or-exp
   (args (list-of expression?))]
  [begin-exp
   (exps (list-of expression?))]
  [case-exp
   (key expression?)
   (keys (list-of expression?))
   (bodies (list-of expression?))
   (else-exp expression?)]
  [case-no-else-exp
   (key expression?)
   (keys (list-of expression?))
   (bodies (list-of expression?))]
  [while-exp
   (test-exp expression?)
   (bodies (list-of expression?))]
  [define-exp
   (id symbol?)
   (def-exp expression?)])



;; environment type definitions

(define scheme-value?
  (lambda (x) #t))


(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)]
  [recursively-extended-env-record
   (proc-names (list-of symbol?))
   (fixed-idss (list-of (list-of symbol?)))
   (variable-idss (list-of (list-of symbol?)))
   (bodiess (list-of (list-of expression?)))
   (env environment?)])


;; datatype for procedures.  At first there is only one
;; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure (vars (list-of symbol?))
           (bodies (list-of expression?))
           (env environment?)]
  [improper-closure (vars (list-of symbol?))
                    (var symbol?)
                    (bodies (list-of expression?))
                    (env environment?)]
  [variable-closure (var symbol?)
                    (bodies (list-of expression?))
                    (env environment?)]
  [k-proc (stored-k continuation?)])


;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


;; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

;; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

;; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

(define parse-exp         
  (lambda (datum)
    (cond
     
     [(null? datum)
      '()]
     
     ;; variable expressions
     [(symbol? datum)
      (var-exp datum)]
     
     ;; literal expressions
     [(literal? datum)
      (cond 
       [(and (pair? datum) (improper? datum))
	(eopl:error 'parse-exp "expression ~s is not a proper list" datum)]
       [(quoted? datum) (lit-exp (2nd datum))]
       [else (lit-exp datum)])]
     
     
     ;; all "list" expressions
     [(pair? datum)
      (cond
       [(improper? datum)
	(eopl:error 'parse-exp "expression ~s is not a proper list" datum)]
       
       ;; cond expressions
       [(equal? (1st datum) 'cond)
	(let* ([has-else (exp-has-else (cdr datum))]
	       [conds-and-exps (if has-else
				   (all-but-last (cdr datum))
				   (cdr datum))]
	       [conditions (map parse-exp (map 1st conds-and-exps))]
	       [exps (map parse-exp (map 2nd conds-and-exps))]
	       [return (if has-else
			   (cond-exp conditions exps (parse-exp (2nd (last (cdr datum)))))
			   (cond-no-else-exp conditions exps))])
	  return)]
       
       ;; and/or expressions
       [(equal? (1st datum) 'and)
	(and-exp (map parse-exp (cdr datum)))]
       
       [(equal? (1st datum) 'or)
	(or-exp (map parse-exp (cdr datum)))]

       ;; begin expression
       [(equal? (1st datum) 'begin)
	(begin-exp (map parse-exp (cdr datum)))]

	   ;; define expression
	   [(equal? (1st datum) 'define)
	(define-exp (2nd datum) (parse-exp (3rd datum)))]
       
       ;; while expressions
       [(equal? (1st datum) 'while)
	(while-exp (parse-exp (2nd datum)) (map parse-exp (cddr datum)))]
       
       ;; case expression
       [(equal? (1st datum) 'case)
	(let* ([key (parse-exp (2nd datum))] 
	       [has-else (exp-has-else (cddr datum))]
	       [keys-and-exps (if has-else
				  (all-but-last (cddr datum))
				  (cddr datum))]
	       [keys (list (parse-exp (list 'quote(map 1st keys-and-exps))))]
	       [bodies (map parse-exp (map 2nd keys-and-exps))]
	       [return (if has-else
			   (case-exp key keys bodies (parse-exp (2nd (last (cddr datum)))))
			   (case-no-else-exp key keys bodies))])
	  return)]
       
       ;; lambda expressions
       [(eqv? (1st datum) 'lambda)
	(cond
	 ;; Check for body
	 [(<= (length datum) 2)
	  (eopl:error 'parse-exp "lambda-expression: incorrect length ~s" datum)]
	 
	 ;; Check for non-symbols in arg list
	 [(and (list? (2nd datum))
	       (not (null? (2nd datum)))
	       (not (andmap symbol? (2nd datum))))
	  (eopl:error 'parse-exp "fixed lambda's formal arguments ~s must all be symbols" datum)]
	 [(and (pair? (2nd datum))
	       (improper? (2nd datum))
	       (not (let ([fixed (get-fixed (2nd datum))] [variable (get-variable (2nd datum))])
		      (and (andmap symbol? fixed) (symbol? variable)))))
	  (eopl:error 'parse-exp "improper lambda's formal arguments ~s must all be symbols" datum)]
	 
	 [(and (not (symbol? (2nd datum))) (not (or (null? (2nd datum)) (pair? (2nd datum)))))
	  (eopl:error 'parse-exp "variable lambda's formal arguments ~s must all be symbols" datum)]
	 
	 
	 ;; Correct types of lambdas
	 [(symbol? (2nd datum))
	  (lambda-variable-exp (2nd datum)
			       (map parse-exp (cddr datum)))]
	 [(and (not (null? (2nd datum))) (improper? (2nd datum)))
	  (lambda-improper-exp (get-fixed (2nd datum)) 
			       (get-variable (2nd datum))
			       (map parse-exp (cddr datum)))]
	 [else
	  (lambda-fixed-exp (2nd datum)
			    (map parse-exp (cddr datum)))])]
       
       ;; if expressions
       [(eqv? (1st datum) 'if)
	(cond
	 ;; Check for body
	 [(<= (length datum) 2)
	  (eopl:error 'parse-exp "if-expression ~s does not have (only) test, then, and else" datum)]
	 
	 [(>= (length datum) 5)
	  (eoapl:error 'parse-exp  "if-expression has incorrect length ~s" datum)]
	 
	 [else
	  (if (null? (cdddr datum))
	      (if-onlythen-exp (parse-exp (2nd datum))
			       (parse-exp (3rd datum)))
	      (if-exp (parse-exp (2nd datum))
		      (parse-exp (3rd datum))
		      (parse-exp (3rd (cdr datum)))))])]
       
       ;; named-let expressions
       [(and (eqv? (1st datum) 'let) (symbol? (2nd datum)))
	(cond
	 ;; declaration are a list
	 [(not (list? (3rd datum)))
	  (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" datum)]
	 
	 ;; improper declaration list
	 [(and (not (null? (3rd datum))) (improper? (3rd datum)))
	  (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" datum)]
	 
	 ;; improper list in declaration
	 [(and (not (null? (3rd datum))) (ormap improper? (3rd datum)))
	  (eopl:error 'parse-exp "declaration in ~s-exp is not a proper list ~s" datum)]
	 
	 ;; no body
	 [(<= (length datum) 3)
	  (eopl:error 'parse-exp  "~s-expression has incorrect length ~s" datum)]
	 
	 ;; All declarations are lists of length 2
	 [(and (not (null? (3rd datum))) (not (andmap (lambda (declaration)
							(= (length declaration) 2))
						      (3rd datum))))
	  (eopl:error 'parse-exp "declaration in ~s-exp must be a list of length 2 ~s" datum)]
	 
	 ;; vars in declaration not symbols
	 [(and (not (null? (3rd datum))) (not (andmap (lambda (declaration)
							(symbol? (car declaration)))
						      (3rd datum))))
	  (eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" datum)]
	 ;; Correct named-let syntax expansion
	 [else
	  (letrec-exp (list (2nd datum)) 
		      (list (map 1st (3rd datum)))
		      '(())
		      (list (map parse-exp (cdddr datum)))
		      (list (parse-exp (cons (2nd datum) 
						 (map 2nd (3rd datum))))))])]
       
       
       ;; let expressions
       [(eqv? (1st datum) 'let)
	(begin
	  (check-let datum)
	  (if (null? (2nd datum))
	      (let-exp
	       '()
	       '()
	       (map parse-exp (cddr datum)))
	      (let-exp
	       (map 1st (2nd datum))
	       (map parse-exp (map 2nd (2nd datum)))
	       (map parse-exp (cddr datum)))))]
       
       ;; let* expressions
       [(eqv? (1st datum) 'let*)
	(begin
	  (check-let datum)
	  (if (null? (2nd datum))
	      (let*-exp
	       '()
	       '()
	       (map parse-exp (cddr datum)))
	      (let*-exp
	       (map 1st (2nd datum))
	       (map parse-exp (map 2nd (2nd datum)))
	       (map parse-exp (cddr datum)))))]
       
       ;; letrec expressions
       [(eqv? (1st datum) 'letrec)
	(begin
	  (check-let datum)
	  (if (null? (2nd datum))
	      (letrec-exp
	       '()
	       '()
	       '()
	       '()
	       (map parse-exp (cddr datum)))
	      (letrec-exp
	       (map 1st (2nd datum))
	       (map (lambda (lambda-exp)
		      (cond
		       [(symbol? (2nd lambda-exp))
			'()]
		       [(and (not (null? (2nd lambda-exp))) 
			     (improper? (2nd lambda-exp)))
			(get-fixed (2nd lambda-exp))]
		       [else
			(2nd lambda-exp)]))
		    (map 2nd (2nd datum)))
	       (map (lambda (lambda-exp)
		      (cond
		       [(symbol? (2nd lambda-exp))
			(list (2nd lambda-exp))]
		       [(and (not (null? (2nd lambda-exp))) 
			     (improper? (2nd lambda-exp)))
			(list (get-variable (2nd lambda-exp)))]
		       [else
			'()]))
		    (map 2nd (2nd datum)))
	       (map (lambda (ls-exp) 
		      (map parse-exp ls-exp))
		    (map cddr (map 2nd (2nd datum))))
	       (map parse-exp (cddr datum)))))]
       
       ;; set! expressions
       [(eqv? (1st datum) 'set!)
	(cond
	 [(<= (length datum) 2)
	  (eopl:error 'parse-exp "set! expression ~s does not have (only) variable and expression" datum)]
	 [(>= (length datum) 4)
	  (eopl:error 'parse-exp  "set! expression has incorrect length ~s" datum)]
	 [else
	  (set!-exp (2nd datum) (parse-exp (3rd datum)))])]
       
       ;; application expressions
       [else
	(cond
	 [(null? (cdr datum))
	  (app-exp (parse-exp (1st datum)) '())]
	 [else
	  (app-exp (parse-exp (1st datum))
		   (map parse-exp (cdr datum)))])])]
     
     ;; improper syntax
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))


(define (check-let exp)
  (cond
   ;; declaration are a list
   [(not (list? (2nd exp)))
    (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" exp)]
   
   ;; improper declaration list
   [(and (not (null? (2nd exp))) (improper? (2nd exp)))
    (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" exp)]
   
   ;; improper list in declaration
   [(and (not (null? (2nd exp))) (ormap improper? (2nd exp)))
    (eopl:error 'parse-exp "declaration in ~s-exp is not a proper list ~s" exp)]

   ;; no body
   [(<= (length exp) 2)
    (eopl:error 'parse-exp  "~s-expression has incorrect length ~s" exp)]
   
   ;; All declarations are lists of length 2
   [(and (not (null? (2nd exp))) (not (andmap (lambda (declaration)
						(= (length declaration) 2))
					      (cadr exp))))
    (eopl:error 'parse-exp "declaration in ~s-exp must be a list of length 2 ~s" exp)]
   
   ;; vars in declaration not symbols
   [(and (not (null? (2nd exp))) (not (andmap (lambda (declaration)
						(symbol? (car declaration)))
					      (2nd exp))))
    (eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" exp)]
   
   [else (void)]))



;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+

;; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env-recursively
  (lambda (proc-names fixed-idss variable-idss bodiess old-env)
    (recursively-extended-env-record
     proc-names fixed-idss variable-idss bodiess old-env)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (map (lambda (val)
    								(if (box? val)
    									val
    									(box val))) vals) env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define apply-env-ref
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (cases environment env
	   [empty-env-record ()
			     (fail)]
	   [extended-env-record (syms vals env)
				(let ((pos (list-find-position sym syms)))
				  (if (number? pos)
				      (succeed (list-ref vals pos))
				      (apply-env-ref env sym succeed fail)))]
	   [recursively-extended-env-record
	    (proc-names fixed-idss variable-idss bodiess old-env)
	    (let ([pos
		   (list-find-position sym proc-names)])
	      (if (number? pos)
		  (begin
		  (let ([fixed-vars (list-ref fixed-idss pos)]
			[variable-vars (list-ref variable-idss pos)]
			[bodies (list-ref bodiess pos)])
		   (succeed (box (cond
		     [(and (null? fixed-vars) 
			   (not (null? variable-vars)))
		      (variable-closure (car variable-vars) bodies env)]
		     [(and (not (null? fixed-vars))
			   (not (null? variable-vars)))
		      (improper-closure fixed-vars (car variable-vars) bodies env)]
		     [else
		      (closure fixed-vars
			       bodies
			       env)])))))
		  (apply-env-ref old-env sym succeed fail)))])))

(define apply-env
	(lambda (env var succeed fail)
		(deref (apply-env-ref env var succeed fail))))

(define deref unbox)
(define set-ref! set-box!)





;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+

(define syntax-expand
  (let ([identity-proc (lambda (x) x)])
    (lambda (exp)
      (cases expression exp
	     [let-exp (vars exps bodies)
		      (app-exp (lambda-fixed-exp vars
						 (map syntax-expand bodies))
			       (map syntax-expand exps))]
	     [letrec-exp (proc-names fixed-idss variable-idss bodiess letrec-bodies)
	     	(letrec-exp proc-names 
	     		fixed-idss 
	     		variable-idss 
	     		(map (lambda (bodies)
	     			(map syntax-expand bodies)) bodiess)
	     		(map syntax-expand letrec-bodies))]
	     [lit-exp (datum) exp]
	     [var-exp (id) (identity-proc exp)]
	     [if-exp (test-exp then-exp else-exp)
		     (if-exp (syntax-expand test-exp)
		     		 (syntax-expand then-exp)
		     		 (syntax-expand else-exp))]
	     [if-onlythen-exp (test-exp then-exp)
			 (if-onlythen-exp (syntax-expand test-exp)
			 				  (syntax-expand then-exp))]
	     [lambda-fixed-exp (vars bodies)
			 (lambda-fixed-exp vars
			 				   (map syntax-expand bodies))]
	     [lambda-improper-exp (vars var bodies)
			 (lambda-improper-exp vars
			 					  var
			 					  (map syntax-expand bodies))]
	     [lambda-variable-exp (var bodies)
		  	 (lambda-variable-exp var
		  	 					  (map syntax-expand bodies))]
	     [app-exp (rator rands)
		      (app-exp (syntax-expand rator)
		      		   (map syntax-expand rands))]
	     [and-exp (args)
		      (and-exp (map syntax-expand args))]
	     [or-exp (args)
		     (or-exp (map syntax-expand args))]
	     [cond-exp (conditions exps else-exp)
		      (cond-exp (map syntax-expand conditions)
		      			(map syntax-expand exps)
		      			(syntax-expand else-exp))]
	     [cond-no-else-exp (conditions exps)
			  (cond-no-else-exp (map syntax-expand conditions)
		      					(map syntax-expand exps))]
	     [let*-exp (vars exps bodies)
		       (syntax-expand (let let*-expand ([vars vars] [exps exps])
					(let-exp (list (car vars)) (list (syntax-expand (car exps)))
						 (if (null? (cdr vars))
						     (map syntax-expand bodies)
						     (list (let*-expand (cdr vars) (cdr exps)))))))]
	     [begin-exp (exps) (begin-exp (map syntax-expand exps))]
	     [define-exp (id def-exp) (define-exp id (syntax-expand def-exp))]
	     [set!-exp (id set-exp) (set!-exp id (syntax-expand set-exp))]
	     [while-exp (test-exp bodies) (while-exp (syntax-expand test-exp) 
	     										 (map syntax-expand bodies))]
	     [case-exp (key keys bodies else-exp) (case-exp (syntax-expand key) 
	     												(map syntax-expand keys) 
	     												(map syntax-expand bodies)
	     												(syntax-expand else-exp))]
	     [case-no-else-exp (key keys bodies) (case-no-else-exp (syntax-expand key)
	     													   (map syntax-expand keys)
	     													   (map syntax-expand bodies))]
	     [else (error 'syntax-expand
			  "Bad parsed expression: ~a" exp)]))))


;-------------------+
;                   |
;   INTERPRETER     |
;                   |
;-------------------+

(define apply-k
	(lambda (k val)
		(cases continuation k
			[test-k (then-exp else-exp env k)
				 	(if val
				 		(eval-exp then-exp env k)
				 		(if (equal? else-exp (void))
				 			(apply-k k (void))
				 			(eval-exp else-exp env k)))]
			[rator-k (rands env k)
					 (eval-rands rands
					 			  env
					 			  (rands-k val k))]
			[rands-k (proc-value k)
					 (apply-proc proc-value val k)]
			[eval-car-k (cdr-bodies env k)
					(if (null? cdr-bodies)
						(apply-k k val)
						(eval-bodies-cps cdr-bodies env
							k))]
			[cond-k (cdr-conds exps else-exp env k)
				(if val
					(eval-exp (1st exps) env k)
					(eval-cond cdr-conds
							   (cdr exps)
							   else-exp
							   env
							   k))]
			[and-k (cdr-args env k)
				(if (not val)
					#f
					(eval-and cdr-args env k))]
			[or-k (cdr-args env k)
				(if val
					val
					(eval-or cdr-args env k))]
			[define-k (id syms vals env k)
				(apply-k k (set! global-env
		 					(extend-env
		 						(cons id syms)
		 						(cons val vals)
		 						env)))]
			[set!-k (id env k)
				(apply-env-ref env 
					 id 
					 (lambda (result)
					 	(apply-k k (set-ref! result val)))
      			 	 (lambda () ; procedure to call if id is not in env
						 (apply-env-ref global-env ; was init-env
    							    id
    							    (lambda (result)
    							    	(apply-k k (set-ref! result val))) ; call if id is in global-env
     							    (lambda () ; call if id not in global-env
										(error 'apply-env-ref
	    									   "variable ~s is not bound"
	       										id)))))]
			[map-cdr-k (car-L proc-cps k)
				(proc-cps car-L
					(map-car-k val k))]
			[map-car-k (mapped-cdr k)
				(apply-k k (cons val mapped-cdr))]
			[eval-key-k (keys bodies else-exp env k)
				(eval-case val keys bodies else-exp env k)]
			[member-case-k (key cdr-keys bodies else-exp env k)
				(if val
					(eval-exp (1st bodies) env k)
					(eval-case key cdr-keys (cdr bodies) else-exp env k))]
			[eval-keys-list-k (key bodies else-exp env k)
				(eval-exp key env
					(eval-key-k val bodies else-exp env k))]
			[while-test-k (test-exp bodies env k)
				(if val
					(eval-bodies-cps bodies env
						(while-bodies-k test-exp bodies env k))
					(apply-k k (void)))]
			[while-bodies-k (test-exp bodies env k)
				(while-loop test-exp bodies env k)]
			[init-k ()
				val])))

(define-datatype continuation continuation?
	(test-k (then-exp expression?)
			(else-exp expression-or-void?)
			(env environment?)
			(k continuation?))
	(rator-k (rands (list-of expression?))
			 (env environment?)
			 (k continuation?))
	(rands-k (proc-value proc-val?)
			 (k continuation?))
	(eval-car-k (cdr-bodies (list-of expression?))
				(env environment?)
				(k continuation?))
	(cond-k (cdr-conds (list-of expression?))
			(exps (list-of expression?))
			(else-exp expression-or-void?)
			(env environment?)
			(k continuation?))
	(and-k (cdr-args (list-of expression?))
		   (env environment?)
		   (k continuation?))
	(or-k (cdr-args (list-of expression?))
		   (env environment?)
		   (k continuation?))
	(define-k (id symbol?)
			  (syms (list-of symbol?))
			  (vals (list-of scheme-value?))
			  (env environment?)
			  (k continuation?))
	(set!-k (id symbol?)
			(env environment?)
			(k continuation?))
	(map-cdr-k (car-L scheme-value?)
			   (proc-cps procedure?)
		  	   (k continuation?))
	(map-car-k (mapped-cdr (list-of scheme-value?))
		 	   (k continuation?))
	(eval-key-k (keys (list-of scheme-value?))
				(bodies (list-of expression?))
				(else-exp expression-or-void?)
				(env environment?)
				(k continuation?))
	(member-case-k (key scheme-value?)
				   (cdr-keys (list-of scheme-value?))
				   (bodies (list-of expression?))
				   (else-exp expression-or-void?)
				   (env environment?)
				   (k continuation?))
	(eval-keys-list-k (key scheme-value?)
				      (bodies (list-of expression?))
				      (else-exp expression-or-void?)
				      (env environment?)
				      (k continuation?))
	(while-test-k (test-exp expression?)
				  (bodies (list-of expression?))
				  (env environment?)
				  (k continuation?))
	(while-bodies-k (test-exp expression?)
				    (bodies (list-of expression?))
				    (env environment?)
				    (k continuation?))
	(init-k))


;; top-level-eval evaluates a form in the global environment


(define top-level-eval
  (lambda (form)
  	(cases expression form
    	[define-exp (id def-exp)
    		((lambda (gl-env)
		 		(cases environment gl-env
		 			[extended-env-record
		 				(syms vals env)
		 				(eval-exp def-exp (empty-env)
		 					(define-k id syms vals env (init-k)))]
		 			[else (error 'define-exp
		 						"incorrect environment ~s" gl-env)]))
		 	global-env)]

    	[else
  	    	(eval-exp form (empty-env) (init-k))])))
	


; (define eval-bodies
;   (lambda (bodies env)
;     (if (null? (cdr bodies))
; 	(eval-exp (car bodies) env)
; 	(begin
; 	  (eval-exp (car bodies) env)
; 	  (eval-bodies (cdr bodies) env)))))

(define eval-bodies-cps
	(lambda (bodies env k)
		(if (null? bodies)
			(apply-k k '())
			(eval-exp (car bodies) env
				(eval-car-k (cdr bodies) env k)))))

(define eval-cond
	(lambda (conds exps else-exp env k)
		(if (null? conds)
			(if (equal? else-exp (void))
				 (apply-k k (void))
				(eval-exp else-exp env k))
			(eval-exp (1st conds) env
				(cond-k (cdr conds)
						exps
						else-exp
						env
						k)))))

(define eval-case
	(lambda (key keys bodies else-exp env k)
		(if (null? keys)
			(if (equal? else-exp (void))
				(apply-k k (void))
				(eval-exp else-exp env k))
				(member-cps key (1st keys)
					(member-case-k key
								 (cdr keys)
								 bodies
								 else-exp
								 env
								 k)))))

(define member-cps
	(lambda (item list continuation)
		(cond
			[(null? list) (apply-k continuation #f)]
			[(equal? item (car list)) (apply-k continuation #t)]
			[else (member-cps item (cdr list) continuation)])))

(define eval-and
	(lambda (args env k)
		(if (null? (cdr args))
			(eval-exp (1st args) env k)
			(eval-exp (1st args) env
				(and-k (cdr args) env k)))))

(define eval-or
	(lambda (args env k)
		(if (null? (cdr args))
			(eval-exp (1st args) env k)
			(eval-exp (1st args) env
				(or-k (cdr args) env k)))))

(define while-loop 
	(lambda (test-exp bodies env k)
		(eval-exp test-exp env
			(while-test-k test-exp bodies env k))))

(define eval-exp
  (let ([identity-proc (lambda (x) x)])
    (lambda (exp env k)
      (cases expression exp
	     [lit-exp (datum) (apply-k k datum)]
	     [var-exp (id) ; look up its value.
		      (apply-env-ref env
				 id
				 (lambda (result)
				 	(apply-k k (deref result))) ; procedure to call if id is in env
				 (lambda () ; procedure to call if id is not in env
				   (apply-env-ref global-env ; was init-env
					      id
					      (lambda (result)
				 			(apply-k k (deref result))) ; call if id is in global-env
					      (lambda () ; call if id not in global-env
						(error 'apply-env
						       "variable ~s is not bound"
						       id)))))]
	     [letrec-exp
	      (proc-names fixed-idss variable-idss bodiess letrec-bodies)
	      (eval-bodies-cps letrec-bodies
			   (extend-env-recursively
			    proc-names fixed-idss variable-idss bodiess env)
			    k)]
	     [if-exp (test-exp then-exp else-exp)
		     (eval-exp test-exp
		     		   env
		     		   (test-k 
		     		   		then-exp
		     		   		else-exp
		     		   		env
		     		   		k))]
	     [if-onlythen-exp (test-exp then-exp)
			      (eval-exp test-exp
		     		   env
		     		   (test-k 
		     		   		then-exp
		     		   		(void)
		     		   		env
		     		   		k))]
	     [lambda-fixed-exp (vars bodies)
			       (apply-k k (closure vars bodies env))]
	     [lambda-improper-exp (vars var bodies)
				  (apply-k k (improper-closure vars var bodies env))]
	     [lambda-variable-exp (var bodies)
				  (apply-k k (variable-closure var bodies env))]
	     [app-exp (rator rands)
		      (eval-exp rator
		      			env
		      			(rator-k rands env k))]
	     [cond-exp (conditions exps else-exp)
		       (eval-cond conditions exps else-exp env k)]
	     [cond-no-else-exp (conditions exps) 
			   (eval-cond conditions exp (void) env k)]
	     [and-exp (args)
		      (eval-and args env k)]
	     [or-exp (args)
		     (eval-or args env k)]
	     [begin-exp (exps)
		   	(eval-bodies-cps exps env k)]
		 [define-exp (id def-exp)
		 	((lambda (gl-env)
		 		(cases environment gl-env
		 			[extended-env-record
		 				(syms vals env)
		 				(eval-exp def-exp (empty-env)
		 					(define-k id syms vals env k))]
		 			[else (error 'define-exp
		 						"incorrect environment ~s" gl-env)]))
		 	global-env)]
		 [set!-exp (id set-exp)
		 	(eval-exp set-exp env
		 		(set!-k id env k))]
	     [while-exp (test-exp bodies)
	     	(while-loop test-exp bodies env k)]
		  ;  	(let while-loop ()
			 ;  (if (eval-exp test-exp env)
			 ;      (begin
				; (eval-bodies bodies env)
				; (while-loop))
			 ;      (void)))]
	     [case-exp (key keys bodies else-exp)
	     	(eval-exp (1st keys) env
	     		(eval-keys-list-k key bodies else-exp env k))]
	     [case-no-else-exp (key keys bodies)
	     	(eval-exp (1st keys) env
	     		(eval-keys-list-k key bodies (void) env k))]
	     [else (error 'eval-exp
			  "Bad abstract syntax: ~a" exp)]))))

;; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env k)
  	(map-cps (lambda (e k1) (eval-exp e env k1)) rands k)))

(define map-cps
	(lambda (proc-cps L k)
		(if (null? L)
			(apply-k k '())
			(map-cps proc-cps (cdr L)
				(map-cdr-k (car L) proc-cps k)))))


;;  Apply a procedure to its arguments.
;;  At this point, we only have primitive procedures.  
;;  User-defined procedures will be added later.

(define sanitize-args
  (lambda (args len pos)
    (if (= len pos)
	(list (car args) (cdr args))
	(cons (car args) (sanitize-args (cdr args) len (+ 1 pos))))))

(define apply-proc
  (lambda (proc-value args k)
    (cases proc-val proc-value
	   [prim-proc (op) (apply-prim-proc op args k)]
	   [closure (vars bodies env)
		    (eval-bodies-cps bodies 
				 (extend-env vars args env) k)]
	   [improper-closure (vars var bodies env)
			     (eval-bodies-cps bodies
					  (extend-env (append vars (list var)) 
						      (sanitize-args args (length vars) 1)
						      env) k)] 
	   [variable-closure (var bodies env)
			     (eval-bodies-cps bodies
					  (extend-env (list var) (list args) env) k)]
       [k-proc (stored-k)
       		(apply-k stored-k (1st args))]
	   ;; You will add other cases
	   [else (eopl:error 'apply-proc
			     "Attempt to apply bad procedure: ~s" 
			     proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 cons = zero? not < >= <= > 
			      car cdr list null? eq? equal? eqv? assq length list->vector list-tail
			      list? pair? procedure? vector vector->list vector? vector-ref vector-set!
			      number? symbol? quotient void display newline call/cc exit-list
			      caar cddr cadr cdar caaar caadr caddr cdddr cdaar cddar cadar cdadr
			      set-car! set-cdr! map apply append))

(define init-env
	(lambda ()         ; for now, our initial global environment only contains 
  		(extend-env            ; procedure names.  Recall that an environment associates
  			 *prim-proc-names*   ;  a value (not an expression) with an identifier.
   				(map prim-proc      
					*prim-proc-names*)
   					(empty-env))))

(define global-env (init-env))

(define reset-global-env
	(lambda () (set! global-env (init-env))))

;; Usually an interpreter must define each 
;; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args k)
    (case prim-proc
      [(void) (apply-k k (void))]
      [(+) (apply-k k (apply + args))]
      [(-) (apply-k k (apply - args))]
      [(*) (apply-k k (apply * args))]
      [(/) (apply-k k (/ (1st args) (2nd args)))]
      [(quotient) (apply-k k (quotient (1st args) (2nd args)))]
      [(zero?) (apply-k k (zero? (1st args)))]
      [(not) (apply-k k (not (1st args)))]
      [(<) (apply-k k (< (1st args) (2nd args)))]
      [(<=) (apply-k k (<= (1st args) (2nd args)))]
      [(>) (apply-k k (> (1st args) (2nd args)))]
      [(>=) (apply-k k (>= (1st args) (2nd args)))]
      [(add1) (apply-k k (+ (1st args) 1))]
      [(sub1) (apply-k k (- (1st args) 1))]
      [(cons) (apply-k k (cons (1st args) (2nd args)))]
      [(car) (apply-k k (car (1st args)))]
      [(cdr) (apply-k k (cdr (1st args)))]
      [(caar) (apply-k k (caar (1st args)))]
      [(cddr) (apply-k k (cddr (1st args)))]
      [(cadr) (apply-k k (cadr (1st args)))]
      [(cdar) (apply-k k (cdar (1st args)))]
      [(caaar) (apply-k k (caaar (1st args)))]
      [(caadr) (apply-k k (caadr (1st args)))]
      [(caddr) (apply-k k (caddr (1st args)))]
      [(cdddr) (apply-k k (cdddr (1st args)))]
      [(cdaar) (apply-k k (cdaar (1st args)))]
      [(cddar) (apply-k k (cddar (1st args)))]
      [(cadar) (apply-k k (cadar (1st args)))]
      [(cdadr) (apply-k k (cdadr (1st args)))]
      [(list) (apply-k k args)]
      [(null?) (apply-k k (null? (1st args)))]
      [(assq) (apply-k k (apply assq args))]
      [(eq?) (apply-k k (eq? (1st args) (2nd args)))]
      [(equal?) (apply-k k (equal? (1st args) (2nd args)))]
      [(eqv?) (apply-k k (eqv? (1st args) (2nd args)))]
      [(atom?) (apply-k k (display "didn't know we needed this!"))]
      [(length) (apply-k k (length (1st args)))]
      [(list->vector) (apply-k k (list->vector (1st args)))]
      [(list?) (apply-k k (list? (1st args)))]
      [(pair?) (apply-k k (pair? (1st args)))]
      [(procedure?) (apply-k k (proc-val? (1st args)))]
      [(vector->list) (apply-k k (vector->list (1st args)))]
      [(make-vector) (apply-k k (display "didn't know we needed this!"))]
      [(vector) (apply-k k (apply vector args))]
      [(vector-ref) (apply-k k (vector-ref (1st args) (2nd args)))]
      [(vector?) (apply-k k (vector? (1st args)))]
      [(number?) (apply-k k (number? (1st args)))]
      [(symbol?) (apply-k k (symbol? (1st args)))]
      [(set-car!) (apply-k k (set-car! (1st args) (2nd args)))] 
      [(set-cdr!) (apply-k k (set-cdr! (1st args) (2nd args)))]
      [(vector-set!) (apply-k k (vector-set! (1st args) (2nd args) (3rd args)))]
      [(display) (apply-k k (apply display args))]
      [(newline) (apply-k k (apply newline args))]
      [(call/cc) (apply-proc (1st args) (list (k-proc k)) k)]
      [(exit-list) args]
      [(map)
       (apply-k k (map-cps (lambda (arg k)
	      (apply-proc (1st args) (list arg) k))
	    (2nd args) k))]
      [(apply) (apply-k k (apply-proc (1st args) (2nd args) k))]
      [(append) (apply-k k (append (1st args) (2nd args)))]
      [(list-tail) (apply-k k (list-tail (1st args) (2nd args)))]
      [(=) (apply-k k (= (1st args) (2nd args)))]
      [else (error 'apply-prim-proc 
		   "Bad primitive procedure name: ~s" 
		   prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))