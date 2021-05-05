(set-logic UFLIA)

(declare-sort Coin 0 )
(declare-sort Address 0)
(declare-fun act (Coin Int) Bool )

(declare-fun hc (Address Coin Int) Bool)

(declare-fun helper (Int) Bool)

(declare-const A1 Address)
(declare-const A2 Address)
(declare-const N Int)

;+-----------------------------+
;| Helper predicate definition |
;+-----------------------------+ 
(assert
    (forall ((I Int))
        (=
            (helper I)
            (and
                (forall ((C Coin))
                    (=
                        (exists ((A Address))
                            (hc A C I)
                        )
                        (act C I)
                    )
                )
                (forall ((A Address) (B Address) (C Coin))
                    (=>
                        (and (hc A C I) (hc B C I))
                        (= A B)
                    )
                )
            )
        )
    )
)

; +------------------+
; | 'Pre'-invariants |
; +------------------+

; inactive coins and at least one
(assert
    (forall ((C Coin))
        (=
            (exists ((A Address))
                (hc A C 0)
            )
            (act C 0)
        )
    )
)

; at most one
(assert
    (forall ((A Address) (B Address) (C Coin))
        (=>
            (and (hc A C 0) (hc B C 0))
            (= A B)
        )
    )
)

; +------------+
; | Transition |
; +------------+
(assert
    (forall ((I Int))
        (=>
            (<= 0 I )
            (and 
                (forall ((C-p Coin))
                    (=
                        (act C-p I)
                        (act C-p (+ I 1))
                    )
                )
                (exists ((C Coin))
                    (and
                        (hc A1 C I)
                        (not (hc A2 C I))
                        (not (hc A1 C (+ I 1)))
                        (hc A2 C (+ I 1))
                        (forall ((C-p Coin) (A-p Address))
                            (=>
                                (or
                                    (distinct C C-p)
                                    (and (distinct A-p A1) (distinct A-p A2) )
                                )
                                (=
                                    (hc A-p C-p (+ I 1))
                                    (hc A-p C-p I)
                                )
                            )
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
    (and
        (<= 0 N)
        (not (helper N))
    )
)

;The exact command is:
;vampire --input_syntax smtlib2  transferN_uf.smt --forced_options "aac=none:add=large:afp=40000:afq=1.2:amm=off:anc=none:bd=off:fsr=off:gsp=input_only:inw=on:irw=on:lma=on:nm=64:nwc=1:sos=on:sp=occurrence:tha=off:updr=off:awr=5:s=1011:sa=discount:ind=math"


(check-sat)
;(get-model)
;(get-info :all-statistics)
