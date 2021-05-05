(set-logic UF)

(declare-sort Coin 0 )
(declare-sort Address 0)
(declare-fun old-act (Coin) Bool )
(declare-fun new-act (Coin) Bool )

(declare-fun old-hc (Address Coin) Bool)
(declare-fun new-hc (Address Coin) Bool)

(declare-const A1 Address)
(declare-const A2 Address)

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
    (and
        (forall ((C-p Coin))
            (=
                (new-act C-p)
                (old-act C-p)
            )
        )
        (exists ((C Coin))
            (and
                (old-hc A1 C)
                (not (old-hc A2 C))
                (not (new-hc A1 C))
                (new-hc A2 C)
                (forall ((C-p Coin) (A-p Address))
                    (=>
                        (or
                            (distinct C-p C)
                            (and
                                (distinct A-p A1)
                                (distinct A-p A2)
                            )
                        )
                        (=
                            (new-hc A-p C-p)
                            (old-hc A-p C-p)
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