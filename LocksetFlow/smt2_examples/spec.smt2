(set-option :fixedpoint.engine datalog)
; This sort is used to define all relations. It is the size of an unsigned on
; the target machine.
(define-sort s () (_ BitVec 32))
; Mutex sort 
(define-sort ms () (_ BitVec 8))

; CFG Flow from-->to
(declare-rel flow (s s))

; A path between two nodes where the start of the path is a mutex lock and
; there does not exist a mutex unlock to the same mutex on the path:
; from-->...->to for a mutex m
;(declare-rel unlock-free-path (s s s))
(declare-rel unlock-free-path (s s ms))

; True if the passed variable represents a mutex lock to a given mutex
(declare-rel is-lock (s ms))

; True if the passed variable represents a mutex unlock to a given mutex
(declare-rel is-unlock (s ms))

; True if the passed variable is not a mutex unlock to the given mutex
(declare-rel is-not-unlock (s ms))

; True if the passed variable is a non-mutex statement (i.e., not a mutex lock
; or unlock) with respect to the passed mutex
(declare-rel is-non-mutex (s))
;(declare-rel is-non-mutex (s ms))

; True if the passed statement has the passed mutex in its lockset
(declare-rel lockset (s ms))


(declare-var from s)
(declare-var to s)
(declare-var pred s)
(declare-var m ms)
(declare-var m2 ms)
(declare-var m3 ms)
(declare-var stmt s)

; a lock statement is not an unlock statement
(rule (=> (is-lock stmt m) (is-not-unlock stmt m)))

; a non mutex statement is not an unlock
(rule (=> (is-non-mutex stmt) (is-not-unlock stmt m)))

; There is an unlock free path to a lock call to iteself
(rule (=> 
        (is-lock to m)
        (unlock-free-path to to m)))

; Base case: there exists a mutex unlock free path for a given mutex if there
; is a mutex_lock() call with a CFG edge to another node which is not a mutex
; unlock
(rule (=> 
        (and 
          (flow from to) 
          (is-lock from m) 
          ; The 'to' node in the CFG edge is not an unlock to the same mutex
          (or (is-non-mutex to) (and (not (= m m2)) (or (is-lock to m2) (is-unlock to m2)))))
        (unlock-free-path from to m)))

; Recursive case: there exists a mutex unlock free path for a given mutex if
; there is a mutex free path leading up to a predecessor of a node
(rule (=>
        (and (flow pred to) 
             ; the predecessor node is not an unlock to the same mutex
             (or (is-non-mutex pred) (and (not (= m m2)) (or (is-lock pred m2) (is-unlock pred m2))))
             ; the to node is not an unlock
             (or (is-non-mutex to) (and (not (= m m2)) (or (is-lock to m2) (is-unlock to m2))))
             (unlock-free-path from pred m))
        (unlock-free-path from to m)))

; A mutex is in the lockset of a given statement if there is an unlock free
; path from another statement to the statement
(rule (=> (unlock-free-path from to m) (lockset to m)))
