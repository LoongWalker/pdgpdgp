(set-option :fixedpoint.engine datalog)

; sort for CFG nodes
(define-sort s () (_ BitVec 32))

; Sort for mutex IDs
(define-sort ms () (_ BitVec 32))

; Sort for thread IDs
(define-sort ts () (_ BitVec 32))

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

; The thread ID of a CFG node (statement)
(declare-rel thread-id (s ts))

; The inter-thread flow edge. This is used for the final CFG but is not used to
; calculate the lockset. TODO: Is there such thing as an inter-thread lockset
; analysis?
(declare-rel inter-flow (s s))

; Two statements are in this relation if they have disjoint locksets
(declare-rel disjoint-locksets (s s))

; Two statements are in this relation if they cannot run in parallel
(declare-rel non-co-en (s s))


; Rules
(declare-var stmt s)
(declare-var pred s)
(declare-var m ms)
(declare-var m1 ms)
(declare-var m2 ms)
(declare-var t1 ts)
(declare-var t2 ts)
(declare-var s1 s)
(declare-var s2 s)

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

; If two statements have lockset relations but they do not overlap then they
; are disjoint
;(rule (=> (and (lockset s1 m1)
;               (lockset s2 m2)
;               (not (= m1 m2)))
;          (disjoint-locksets s1 s2)))

(rule (=> (and (lockset s1 m1)
               (lockset s2 m2)
               (= m1 m2))
               (non-co-en s1 s2)))
            


; There is a inter-thread flow edge between two nodes from different threads
; with disjoint locksets
(rule (=> (and 
                (thread-id s1 t1)
                (thread-id s2 t2)
                (not (= t1 t2))
                ;(disjoint-locksets s1 s2))
                (not (non-co-en s1 s2)))
          (inter-flow s1 s2)))

; Begin facts

;;;;;; Thread zero facts
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

(rule (thread-id #x00000000 #x00000000))
(rule (thread-id #x00000001 #x00000000))
(rule (thread-id #x00000002 #x00000000))
(rule (thread-id #x00000003 #x00000000))
(rule (thread-id #x00000004 #x00000000))
(rule (thread-id #x00000005 #x00000000))
(rule (thread-id #x00000006 #x00000000))

;;;;;; End thread zero facts
;;;;;; Begin thread one facts
(rule (is-lock #x00000007 #x000000FF))
(rule (is-non-mutex #x00000008))
(rule (is-unlock #x00000009 #x000000FF))
(rule (is-non-mutex #x0000000A))

(rule (flow #x00000007 #x00000008))
(rule (flow #x00000008 #x00000009))
(rule (flow #x00000009 #x0000000A))

(rule (thread-id #x00000007 #x00000001))
(rule (thread-id #x00000008 #x00000001))
(rule (thread-id #x00000009 #x00000001))
(rule (thread-id #x0000000A #x00000001))
;;;;;; End thread one facts


; End facts

(query (lockset #x00000000 m)
  :print-answer true)
;(query (lockset #x00000001 m)
;  :print-answer true)
;(query (lockset #x00000002 m) 
;  :print-answer true)
;(query (lockset #x00000003 m)
;  :print-answer true)
;(query (lockset #x00000004 m)
;  :print-answer true)
;(query (lockset #x00000005 m)
;  :print-answer true)
;(query (lockset #x00000006 m)
;  :print-answer true)
;(query (lockset #x00000007 m)
;  :print-answer true)
;(query (lockset #x00000008 m)
;  :print-answer true)
;(query (lockset #x00000009 m)
;  :print-answer true)
(query (lockset #x0000000A m)
  :print-answer true)

(query (inter-flow #x0000000A #x00000000)
  :print-answer true)
(query (inter-flow #x00000008 #x00000001)
  :print-answer true)

(query (inter-flow s1 s2)
  :print-answer true)
