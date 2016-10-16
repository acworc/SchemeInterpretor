;; Trinity Merrell
;; Chris Samp
;; Assignment A11b

(load "chez-init.ss"); This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

;; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

;; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

(define check-improper?
  (lambda (ls)
    (and (improper? ls) (check-improper? (cdr ls)))))

(define (improper? pair)
  (if (and (not (null? pair))
	   (not (eq?   (cdr pair) '()))
	   (not (pair? (cdr pair))))
      #t
      (if (null? (cdr pair))
	  #f
	  (improper? (cdr pair)))))

(define parse-exp         
  (lambda (datum)
    (cond
     
     [(null? datum)
      (empty-exp)]
     
     ;; variable expressions
     [(symbol? datum)
      (var-exp datum)]
     
     ;; literal expressions
     [(literal? datum)
      (cond 
       [(and (pair? datum) (improper? datum))
	(eopl:error 'parse-exp "expression ~s is not a proper list" datum)]
       [else (lit-exp datum)])]

     
     ;; all "list" expressions
     [(pair? datum)
      (cond
       [(improper? datum)
	(eopl:error 'parse-exp "expression ~s is not a proper list" datum)]
       
       ;; lambda expressions
       [(eqv? (1st datum) 'lambda)
	(cond
	 ;; Check for body
	 [(<= (length datum) 2)
	  (eopl:error 'parse-exp "lambda-expression: incorrect length ~s" datum)]
	 
	 ;; Check for non-symbols in arg list
	 [(or (and (list? (2nd datum))
		   (not (null? (2nd datum)))
		   (not (andmap (lambda (n)
				  (symbol? n))
				(2nd datum))))
	      (not (or (list? (2nd datum))
		       (symbol? (2nd datum)))))
	  (eopl:error 'parse-exp "lambda's formal arguments ~s must all be symbols" datum)]

	 ;; Correct types of lambdas
	 [(symbol? (2nd datum))
	  (lambda-variable-exp (2nd datum)
			       (map parse-exp (cddr datum)))]
	 [(and (not (null? (2nd datum))) (improper? (2nd datum)))
	  (lambda-improper-exp (2nd datum)
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
	  (eopl:error 'parse-exp  "if-expression has incorrect length ~s" datum)]
	 
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
	 [(and (not? (null? (3rd datum))) (improper? (3rd datum)))
	  (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" datum)]
	 
	 ;; improper list in declaration
	 [(and (not? (null? (3rd datum))) (ormap improper? (3rd datum)))
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
	      (namedlet-exp (2nd datum)
			    '()
			    '()
			    (map parse-exp (cdddr datum)))
	      (namedlet-exp (2nd datum) (map 1st (3rd datum))
			    (map parse-exp (map 2nd (3rd datum)))
			    (map parse-exp (cdddr datum))))])]

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
	       (map parse-exp (cddr datum)))
	      (letrec-exp
	       (map 1st (2nd datum))
	       (map parse-exp (map 2nd (2nd datum)))
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
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

(define unparse-exp
  (lambda (exp)
    (cases expression exp
	   [empty-exp () '()]
	   [var-exp (id) id]
	   [lit-exp (id) id]
	   [lambda-variable-exp (id bodies)
				(append (list 'lambda
				      id)
				      (map unparse-exp bodies))] ; variable length args
	   [lambda-improper-exp (ids bodies)
				(append (list 'lambda
				      ids)
				      (map unparse-exp bodies))] ; Improper length args
	   [lambda-fixed-exp (ids bodies)
			     (append (list 'lambda
				   ids)
				   (map unparse-exp bodies))] ; fixed length args
	   [if-exp (condition if-true if-false)
		   (list 'if
			 (unparse-exp condition)
			 (unparse-exp if-true)
			 (unparse-exp if-false))]
	   [if-onlythen-exp (condition if-true)
			    (list 'if
				  (unparse-exp condition)
				  (unparse-exp if-true))]
	   
	   [namedlet-exp (id varids varexps bodies)
			 (append (list 'let
			       id
			       (unparse-let-vars varids varexps))
			       (map unparse-exp bodies))]
	   
	   [let-exp (varids varexps bodies)
		    (append (list 'let
			  (unparse-let-vars varids varexps))
			  (map unparse-exp bodies))]
	   
	   [let*-exp (varids varexps bodies)
		     (append (list 'let*
			   (unparse-let-vars varids varexps))
			   (map unparse-exp bodies))]
	   
	   [letrec-exp (varids varexps bodies)
		       (append (list 'letrec
			     (unparse-let-vars varids varexps))
			     (map unparse-exp bodies))]
	   
	   [set!-exp (id exp)
		     (append (list 'set!
			   id)
			   (unparse-exp exp))]
	   
	   [app-exp (rator rands)
		    (append (list (unparse-exp rator))
			  (map unparse-exp rands))])))

(define (literal? var)
  (or (symbol? var)
      (boolean? var)
      (string? var)
      (number? var)
      (vector? var)
      (quoted-list? var)))

(define (quoted-list? var)
  (and (list? var)
       (eq? (1st var) 'quote)))

(define (unparse-let-vars vars vals)
  (cond
   [(null? vars)
    '()]
   [else (cons (list (car vars) (unparse-exp (car vals))) (unparse-let-vars (cdr vars) (cdr vals)))]))

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
  
(define-datatype expression expression?
  [empty-exp]
  [var-exp
   (id symbol?)]
  [lambda-variable-exp
   (ids symbol?)
   (bodies (list-of expression?))]
  [lambda-improper-exp
   (ids (list-of symbol?))
   (bodies (list-of expression?))]
  [lambda-fixed-exp
   (ids (list-of symbol?))
   (bodies (list-of expression?))]
  [app-exp
   (rator expression?)
   (rands (list-of expression?))]
  [lit-exp
   (id literal?)] ; Expand to include other variable types
  [if-exp
   (condition expression?)
   (if-true expression?)
   (if-false expression?)]
  [if-onlythen-exp
   (condition expression?)
   (if-true expression?)]
  [let-exp
   (varids (list-of symbol?))
   (varexps (list-of expression?))
   (bodies (list-of expression?))]
  [let*-exp
   (varids (list-of symbol?))
   (varexps (list-of expression?))
   (bodies (list-of expression?))]
  [letrec-exp
   (varids (list-of symbol?))
   (varexps (list-of expression?))
   (bodies (list-of expression?))]
  [namedlet-exp
   (id symbol?)
   (varids (list-of symbol?))
   (varexps (list-of expression?))
   (bodies (list-of expression?))]
  [set!-exp
   (id symbol?)
   (exp expression?)])
