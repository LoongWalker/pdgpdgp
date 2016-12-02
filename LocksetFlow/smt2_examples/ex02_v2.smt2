(set-option :fixedpoint.engine datalog)

; sort for CFG nodes
(define-sort s () (_ BitVec 32))
; Sort for mutex IDs
(define-sort ms () (_ BitVec 32))

; CFG Flow from-->to
(declare-rel flow (s s))

; True if the variable represents a mutex lock to a given mutex
(declare-rel is-lock (s ms))

; True if the  variable represents a mutex unlock to a given mutex
(declare-rel is-unlock (s ms))

; True if the source line is neither a lock nor unlock
(declare-rel is-non-mutex (s))

; The source line's lockeset contains the mutex
(declare-rel lockset (s ms))

; Rules
(declare-var stmt s)
(declare-var pred s)
(declare-var m ms)
(declare-var m1 ms)
(declare-var m2 ms)

; A lock call adds a lock to the lockset
(rule (=> (is-lock stmt m) (lockset stmt m)))

; A lock call also gets the lockset of its predecessor
(rule (=> (and 
            (is-lock stmt m1) 
            (flow pred stmt) 
            (lockset pred m2)) 
          (lockset stmt m2)))

; An unlock call gets all its predecessors locks except if they are being
; unlocked
(rule (=> (and 
            (is-unlock stmt m1) 
            (flow pred stmt) 
            (lockset pred m2)) 
            (not (= m1 m2))
          (lockset stmt m2)))

; Neither an unlock nor lock statement just gets all the locks of its
; predecessor
(rule (=> (and 
            (is-non-mutex stmt) 
            (flow pred stmt) 
            (lockset pred m2)) 
          (lockset stmt m2)))

; Begin facts

(rule (is-lock #x00000000 #x000000FF))

(rule (is-non-mutex #x00000001))

(rule (is-lock #x00000002 #x000000FE))

(rule (is-unlock #x00000003 #x000000FF))

(rule (is-non-mutex #x00000004))

(rule (is-unlock #x00000005 #x000000FE))

(rule (is-non-mutex #x00000006))

(rule (flow #x00000000 #x00000001))
(rule (flow #x00000001 #x00000002))
(rule (flow #x00000001 #x00000003))
(rule (flow #x00000000 #x00000003))
(rule (flow #x00000002 #x00000004))
(rule (flow #x00000004 #x00000005))
(rule (flow #x00000003 #x00000006))
(rule (flow #x00000005 #x00000006))

; End facts

(query (lockset #x00000000 m)
  :print-answer true)
(query (lockset #x00000001 m)
  :print-answer true)
(query (lockset #x00000002 m) 
  :print-answer true)
(query (lockset #x00000003 m)
  :print-answer true)
(query (lockset #x00000004 m)
  :print-answer true)
(query (lockset #x00000005 m)
  :print-answer true)
(query (lockset #x00000006 m)
  :print-answer true)
