; Begin facts

(rule (is-lock #x00000000 #xFF))

(rule (is-non-mutex #x00000001))

(rule (is-lock #x00000002 #xFE))

(rule (is-unlock #x00000003 #xFF))

(rule (is-non-mutex #x00000004))

(rule (is-unlock #x00000005 #xFE))

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


;(query (unlock-free-path #x00000000 #x00000004 #x10000000))
;(query (unlock-free-path #x00000000 #x00000005 #x10000000))
;(query (is-unlock #x00000005 m3))
;  :print-answer true)

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
