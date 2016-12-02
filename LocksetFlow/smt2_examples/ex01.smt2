; Begin facts

;(rule (is-lock #x00000000 #xFF))
(rule (is-lock #x00000000 #xFF))

;(rule (is-unlock #x00000001 #x10000000))
(rule (is-unlock #x00000001 #xFF))

(rule (is-non-mutex #x00000002))
;(rule (is-non-mutex #x00000002 #x10000000))

(rule (is-non-mutex #x00000003))
;(rule (is-non-mutex #x00000003 #x10000000))

(rule (flow #x00000000 #x00000001))
(rule (flow #x00000000 #x00000002))
(rule (flow #x00000001 #x00000002))
(rule (flow #x00000002 #x00000003))

; End facts


;(query (unlock-free-path #x00000000 #x00000000 #x10000000))
;;  :print-answer true)
;(query (unlock-free-path #x00000000 #x00000001 #x10000000))
;(query (unlock-free-path #x00000000 #x00000002 #x10000000))
;(query (unlock-free-path #x00000000 #x00000003 #x10000000))
;(query (unlock-free-path #x00000001 #x00000003 #x10000000))

(query (lockset #x00000000 m)
  :print-answer true)
(query (lockset #x00000001 m)
  :print-answer true)
(query (lockset #x00000002 m)
  :print-answer true)
(query (lockset #x00000003 m)
  :print-answer true)


