(set-logic UF)

(declare-sort Coin 0 )
(declare-sort Address 0)
(declare-fun old-act (Coin) Bool )
(declare-fun new-act (Coin) Bool )

(declare-fun old-hc (Address Coin) Bool)
(declare-fun new-hc (Address Coin) Bool)

(declare-const A1 Address)

; +----------------+
; | Pre-invariants |
; +----------------+

; inactive coins and at least one
(assert
    (forall ((C Coin))
        (=
            (exists ((A Address))
                (old-hc A C)
            )
            (old-act C)
        )
    )
)

; at most one
(assert
    (forall ((A Address) (B Address) (C Coin))
        (=>
            (and (old-hc A C) (old-hc B C))
            (= A B)
        )
    )
)

; +------------+
; | Transition |
; +------------+
(assert
    (exists ((C Coin))
        (and
            (not (old-act C))
            (new-act C)
            (forall ((A Address)) (not (old-hc A C)) )
            (new-hc A1 C)
            (forall ((C-p Coin) (A-p Address))
                (=>
                    (or
                        (distinct C C-p)
                        (distinct A1 A-p)
                    )
                    (and
                        (=
                            (new-hc A-p C-p)
                            (old-hc A-p C-p)
                        )
                        (=
                            (new-act C-p)
                            (old-act C-p)
                        )
                    )
                )
            )
        )
    )
)

; +----------------+
; | Post-invariant |
; +----------------+
(assert
    (not 
        (and
            (forall ((C Coin))
                (=
                    (exists ((A Address))
                        (new-hc A C)
                    )
                    (new-act C)
                 )
            )
            (forall ((A Address) (B Address) (C Coin))
                (=>
                    (and (new-hc A C) (new-hc B C))
                    (= A B)
                )
            )
        )
    )
)

(check-sat)
;(get-model)
;(get-info :all-statistics)