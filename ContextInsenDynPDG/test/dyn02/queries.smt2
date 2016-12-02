;; Some test queries 
;;; Queries

; %4, add() function pointer in main(): #x00000045
; %8, sub() function pointer in main(): #x0000004b
; @add(): #x0000003f
; @sub(): #x00000042

; Does the add function pointer in main point to add()?
; Should be SAT
(query (points-to #x00000045 #x0000003f))

; Does the add function pointer in main point to sub()?
; Should be UNSAT
(query (points-to #x00000045 #x00000042))

; Does the sub function pointer in main point to sub()?
; Should be SAT
(query (points-to #x0000004b #x00000042))

; Does the sub function pointer in main point to add()?
; Should be UNSAT
(query (points-to #x0000004b #x0000003f))

; Is the return of main() dependent on the return of sub()?
; Should be SAT
; 
; ret of sub(): #x0000001c
; ret of main(): #x00000054
(query (prog-dep #x00000054 #x0000001c))

; Is the return of main() dependent on the return of add)?
; Should be SAT
; 
; ret of add(): #x0000001c
(query (prog-dep #x00000054 #x0000000d))

; Is the return of main() dependent on argc?
; Should be UNSAT
; 
; argc: #x00000033
(query (prog-dep #x00000054 #x00000033))
