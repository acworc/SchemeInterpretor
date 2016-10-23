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
   (idss (list-of (list-of symbol?)))
   (bodiess (list-of (list-of expression?)))
   (letrec-bodies (list-of expression?))]
  [namedlet-exp
   (id symbol?)
   (vars (list-of symbol?))
   (exps (list-of expression?))
   (bodies (list-of expression?))]
  [set!-exp
   (id symbol?)
   (exp expression?)]
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
  	(bodies (list-of expression?))])



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
	(idss (list-of (list-of symbol?)))
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
                    (env environment?)])	 


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

		;cond expressions
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

		;and/or expressions
		[(equal? (1st datum) 'and)
			(and-exp (map parse-exp (cdr datum)))]

		[(equal? (1st datum) 'or)
			(or-exp (map parse-exp (cdr datum)))]

		;begin expression
		[(equal? (1st datum) 'begin)
			(begin-exp (map parse-exp (cdr datum)))]

		;while expressions
		[(equal? (1st datum) 'while)
			(while-exp (parse-exp (2nd datum)) (map parse-exp (cddr datum)))]

		;case expression
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
	 
	 [else
	  (if (null? (3rd datum))
	  	  (letrec-exp (list (2nd datum))
	  	  			  '()
	  	  			  (list (map parse-exp (cdddr datum)))
	  	  			  (list (parse-exp (list (2nd datum)))))
	      (letrec-exp (list (2nd datum)) 
	      			  (list (map 1st (3rd datum))) 
	      			  (list (map parse-exp (cdddr datum))) 
	  				  (list (parse-exp (cons (2nd datum) 
	  				  			(map 2nd (3rd datum)))))))])]
	      
       
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
	       (map parse-exp (cddr datum)))
	      (letrec-exp
	       (map 1st (2nd datum))
	       (map 2nd (map 2nd (2nd datum)))
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
	(lambda (proc-names idss bodiess old-env)
	(recursively-extended-env-record
	proc-names idss bodiess old-env)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

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

(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (cases environment env
	   [empty-env-record ()
			     (fail)]
	   [extended-env-record (syms vals env)
				(let ((pos (list-find-position sym syms)))
				  (if (number? pos)
				      (succeed (list-ref vals pos))
				      (apply-env env sym succeed fail)))]
	   [recursively-extended-env-record
			(proc-names idss bodiess old-env)
			(let ([pos
				(list-find-position sym proc-names)])
				(if (number? pos)
					(closure (list-ref idss pos)
						(list-ref bodiess pos)
						env)
			(apply-env old-env sym succeed fail)))])))




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
			[letrec-exp (proc-names idss bodiess letrec-bodies)
				(identity-proc exp)]
			[lit-exp (datum) exp]
	        [var-exp (id) (identity-proc exp)]
	        [if-exp (test-exp then-exp else-exp)
		        (identity-proc exp)]
	        [if-onlythen-exp (test-exp then-exp)
		        (identity-proc exp)]
	        [lambda-fixed-exp (vars bodies)
			    	(identity-proc exp)]
	        [lambda-improper-exp (vars var bodies)
						(identity-proc exp)]
	        [lambda-variable-exp (var bodies)
						(identity-proc exp)]
	        [app-exp (rator rands)
		        (identity-proc exp)]
		    [and-exp (args)
		      	(identity-proc exp)]
		    [or-exp (args)
		      	(identity-proc exp)]
		    [cond-exp (conditions exps else-exp)
		     		(identity-proc exp)]
		    [cond-no-else-exp (conditions exps)
		     		(identity-proc exp)]
	     	[let*-exp (vars exps bodies)
	     		(syntax-expand (let let*-expand ([vars vars] [exps exps])
	     			(let-exp (list (car vars)) (list (syntax-expand (car exps)))
	     				(if (null? (cdr vars))
	     					(map syntax-expand bodies)
	     					(list (let*-expand (cdr vars) (cdr exps)))))))]
	     	[begin-exp (exps) (identity-proc exp)]
	     	[while-exp (test-exp bodies) (identity-proc exp)]
	     	[case-exp (key keys bodies else-exp) (identity-proc exp)]
	     	[case-no-else-exp (key keys bodies) (identity-proc exp)]
			[else (error 'syntax-expand
				  "Bad parsed expression: ~a" exp)]))))


;-------------------+
;                   |
;   INTERPRETER     |
;                   |
;-------------------+

;; top-level-eval evaluates a form in the global environment


(define top-level-eval
  (lambda (form)
    ;; later we may add things that are not expressions.
    (eval-exp form (empty-env))))


(define eval-bodies
  (lambda (bodies env)
    (if (null? (cdr bodies))
	(eval-exp (car bodies) env)
	(begin
	  (eval-exp (car bodies) env)
	  (eval-bodies (cdr bodies) env)))))

					; eval-exp is the main component of the interpreter

(define eval-exp
  (let ([identity-proc (lambda (x) x)])
    (lambda (exp env)
      (cases expression exp
	     [lit-exp (datum) datum]
	     [var-exp (id) ; look up its value.
		      (apply-env env
				 id
				 identity-proc ; procedure to call if id is in env
				 (lambda () ; procedure to call if id is not in env
				   (apply-env global-env ; was init-env
					      id
					      identity-proc ; call if id is in global-env
					      (lambda () ; call if id not in global-env
						(error 'apply-env
						       "variable ~s is not bound"
						       id)))))]
	     [let-exp (vars exps bodies)
		      (let ([new-env (extend-env vars 
						 (eval-rands exps env) 
						 env)])
			(eval-bodies bodies new-env))]
		 [letrec-exp
		 	(proc-names idss bodiess letrec-bodies)
		 	(eval-bodies letrec-bodies
		 		(extend-env-recursively
		 			proc-names idss bodiess env))]
	     [if-exp (test-exp then-exp else-exp)
		     (if (eval-exp test-exp env)
			 (eval-exp then-exp env)
			 (eval-exp else-exp env))]
	     [if-onlythen-exp (test-exp then-exp)
			      (if (eval-exp test-exp env)
				  (eval-exp then-exp env)
				  (void))]
	     [lambda-fixed-exp (vars bodies)
			       (closure vars bodies env)]
	     [lambda-improper-exp (vars var bodies)
				  (improper-closure vars var bodies env)]
	     [lambda-variable-exp (var bodies)
				  (variable-closure var bodies env)]
	     [app-exp (rator rands)
		      (let ([proc-value (eval-exp rator env)]
			    [args (eval-rands rands env)])
			(apply-proc proc-value args))]
		   [cond-exp (conditions exps else-exp)
		   	(let eval-cond ([conditions conditions] [exps exps])
		   		(cond
		   			[(null? conditions) (eval-exp else-exp env)]
		   			[(eval-exp (1st conditions) env)
		   				(eval-exp (1st exps) env)]
		   			[else (eval-cond (cdr conditions) (cdr exps))]))]
		   [cond-no-else-exp (conditions exps) 
		   	(let eval-cond ([conditions conditions] [exps exps])
		   		(cond
		   			[(null? conditions) (void)]
		   			[(eval-exp (1st conditions) env)
		   				(eval-exp (1st exps) env)]
		   			[else (eval-cond (cdr conditions) (cdr exps))]))]
		   [and-exp (args)
		   	(let eval-and ([args args])
		   		(cond 
		   			[(null? (cdr args)) (eval-exp (car args) env)]
		   			[(not (eval-exp (car args) env)) #f]
		   			[else
		   				(eval-and (cdr args))]))]
		   [or-exp (args)
		   	(let eval-or ([args args])
		   		(cond 
		   			[(null? args) #f]
		   			[(eval-exp (car args) env) (eval-exp (car args) env)]
		   			[else 
		   				(eval-or (cdr args))]))]
		   [begin-exp (exps)
		   	(eval-bodies exps env)]
		   [while-exp (test-exp bodies)
		   	(let while-loop ()
			   	(if (eval-exp test-exp env)
			   		(begin
			   			(eval-bodies bodies env)
			   			(while-loop))
			   		(void)))]
		   [case-exp (key keys bodies else-exp)
		   	(let case-eval ([key (eval-exp key env)] [keys (eval-exp (1st keys) env)] [bodies bodies])
		   		(cond
		   			[(null? keys) 
		   				(eval-exp else-exp env)]
		   			[(member key (1st keys))
		   				(eval-exp (car bodies) env)]
		   			[else 
		   				(case-eval key (cdr keys) (cdr bodies))]))]
		   [case-no-else-exp (key keys bodies)
		   	(let case-no-else-eval ([key (eval-exp key env)] [keys (eval-exp (1st keys) env)] [bodies bodies])
		   		(cond
		   			[(null? keys) 
		   				(void)]
		   			[(member key (1st keys))
		   				(eval-exp (car bodies) env)]
		   			[else 
		   				(case-no-else-eval key (cdr keys) (cdr bodies))]))]
	     [else (error 'eval-exp
			  "Bad abstract syntax: ~a" exp)]))))

;; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (e)
	   (eval-exp e env)) rands)))

;;  Apply a procedure to its arguments.
;;  At this point, we only have primitive procedures.  
;;  User-defined procedures will be added later.

(define sanitize-args
	(lambda (args len pos)
		(if (= len pos)
			(list (car args) (cdr args))
			(cons (car args) (sanitize-args (cdr args) len (+ 1 pos))))))

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
	   [prim-proc (op) (apply-prim-proc op args)]
	   [closure (vars bodies env)
		    (eval-bodies bodies 
				 (extend-env vars args env))]
	   [improper-closure (vars var bodies env)
			     (eval-bodies bodies
					  (extend-env (append vars (list var)) 
					  	(sanitize-args args (length vars) 1)
					   env))] 
	   [variable-closure (var bodies env)
			     (eval-bodies bodies
					  (extend-env (list var) (list args) env))]
					; You will add other cases
	   [else (eopl:error 'apply-proc
			     "Attempt to apply bad procedure: ~s" 
			     proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 cons = zero? not < >= <= > 
			      car cdr list null? eq? equal? eqv? length list->vector list-tail
			      list? pair? procedure? vector vector->list vector? vector-ref vector-set!
			      number? symbol? quotient void
			      caar cddr cadr cdar caaar caadr caddr cdddr cdaar cddar cadar cdadr
			      set-car! set-cdr! map apply append))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
   *prim-proc-names*   ;  a value (not an expression) with an identifier.
   (map prim-proc      
	*prim-proc-names*)
   (empty-env)))

(define global-env init-env)

;; Usually an interpreter must define each 
;; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
    	[(void) (void)]
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (/ (1st args) (2nd args))]
      [(quotient) (quotient (1st args) (2nd args))]
      [(zero?) (zero? (1st args))]
      [(not) (not (1st args))]
      [(<) (< (1st args) (2nd args))]
      [(<=) (<= (1st args) (2nd args))]
      [(>) (> (1st args) (2nd args))]
      [(>=) (>= (1st args) (2nd args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(car) (car (1st args))]
      [(cdr) (cdr (1st args))]
      [(caar) (caar (1st args))]
      [(cddr) (cddr (1st args))]
      [(cadr) (cadr (1st args))]
      [(cdar) (cdar (1st args))]
      [(caaar) (caaar (1st args))]
      [(caadr) (caadr (1st args))]
      [(caddr) (caddr (1st args))]
      [(cdddr) (cdddr (1st args))]
      [(cdaar) (cdaar (1st args))]
      [(cddar) (cddar (1st args))]
      [(cadar) (cadar (1st args))]
      [(cdadr) (cdadr (1st args))]
      [(list) (apply list args)]
      [(null?) (null? (1st args))]
      [(assq) (apply assq args)]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(eqv?) (eqv? (1st args) (2nd args))]
      [(atom?) (display "didn't know we needed this!")]
      [(length) (length (1st args))]
      [(list->vector) (list->vector (1st args))]
      [(list?) (list? (1st args))]
      [(pair?) (pair? (1st args))]
      [(procedure?) (proc-val? (1st args))]
      [(vector->list) (vector->list (1st args))]
      [(make-vector) (display "didn't know we needed this!")]
      [(vector) (apply vector args)]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector?) (vector? (1st args))]
      [(number?) (number? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(set-car!) (set-car! (1st args) (2nd args))] 
      [(set-cdr!) (set-cdr! (1st args) (2nd args))] 
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(display) (display "didn't know we needed this!")]
      [(newline) (display "didn't know we needed this!")]
      [(map)
       (map (lambda (arg)
	      (apply-proc (1st args) (list arg)))
	      (2nd args))]
      [(apply) (apply (eval (2nd (1st args))) (2nd args))]
      [(append) (append (1st args) (2nd args))]
      [(list-tail) (list-tail (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
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
