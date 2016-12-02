;; Some test queries 

;;; Queries

; %5: #x00000030, first arg to call in main()
; %6: #x00000031, second arg to call in main()
; %4: #x0000002f, function pointer in main()
; @add(): #x0000002c
; %a: #x00000004, first arg to add()
; %b: #x00000007, second arg to add()

; Does the call-site argument point to the function argument?
; should be SAT
(query (points-to #x00000004 #x00000030))

; second argument, should be SAT
(query (points-to #x00000007 #x00000031))

; Does the first argument point to the second callsite argument?
; Should be UNSAT
(query (points-to #x00000004 #x00000031))

; does the function pointer in main point to the add() function?
; should be SAT
(query (points-to #x0000002f #x0000002c))

; Is the return of the add() function dependent on the first argument of the
; call in main()?
; Should be SAT
;
; ret in add(): #x0000000d
(query (points-to #x0000000d #x00000030))
(query (prog-dep #x0000000d #x00000030))

; Does the return in main depend on the return of add()
; Should be SAT
; ret in main(): #x00000036
(query (prog-dep #x00000036 #x0000000d))

; Does the return in main depend on the value of %a in main()
; Should be SAT
;
; %a in main(): #x00000017
(query (prog-dep #x00000036 #x00000017))
