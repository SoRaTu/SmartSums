(set-logic UFLIA)

(declare-sort Coin 0 )
(declare-sort Address 0)
(declare-fun old-sum () Int)
(declare-fun new-sum () Int)
(declare-fun a0 () Address)
(declare-fun a1 () Address)

(declare-fun old-bal (Address) Int)
(declare-fun new-bal (Address) Int)
(declare-fun count (Coin) Int)
(declare-fun ind (Coin Address) Int)


; #########################################################################################
; ########################  Intra-block axioms for macro world  ###########################
; #########################################################################################

;                                M1''
(assert
    (<= 0 old-sum)
)
(assert
    (<= 0 new-sum)
)

;                                M2''
(assert
    (forall ((C Coin))
        (< 0 (count C))
    )
)

;                                M3''
(assert
    (forall ((C Coin) (D Coin))
        (=>
            (= (count C) (count D))
            (= C D)
        )
    )
)

;                                weakend M4''
(assert
    (exists ((C Coin))
        (= (count C) old-sum)
    )
)
(assert
    (exists ((C Coin))
        (= (count C) new-sum)
    )
)

; #########################################################################################
; #########################  intra-block axioms for micro world ###########################
; #########################################################################################

;                                m1''
(assert
    (forall ((A Address))
        (<= 0 (old-bal A))
    )
)
(assert
    (forall ((A Address))
        (<= 0 (new-bal A))
    )
)

;                                m2''
(assert
    (forall ((C Coin)(A Address))
        (< 0 (ind C A))
    )
)

;                                m3''
(assert
    (forall ((C Coin) (D Coin) (A Address))
        (=>
            (= (ind C A) (ind D A))
            (= C D)
        )
    )
)

;                                weakend m4''
(assert
        (exists ((C Coin )) 
            (= (ind C a0) (old-bal a0))
        )
)
(assert
        (exists ((C Coin))
            (= (ind C a0) (+(old-bal a0) 1))
        )
)
(assert
        (exists ((C Coin))
            (= (ind C a0) (+(old-bal a0) 2))
        )
)
(assert
        (exists ((C Coin))
            (= (ind C a0) (+(old-bal a0) 3))
        )
)

(assert
        (exists ((C Coin )) 
            (= (ind C a1) (new-bal a1))
        )
)
(assert
        (exists ((C Coin))
            (= (ind C a1) (+(new-bal a1) 1))
        )
)
(assert
        (exists ((C Coin))
            (= (ind C a1) (+(new-bal a1) 2))
        )
)
(assert
        (exists ((C Coin))
            (= (ind C a1) (+(new-bal a1) 3))
        )
)


; #########################################################################################
; ##################################  inter-block axioms  #################################
; #########################################################################################

;                                I1''
(assert
    (forall ((C Coin))
        (=
            (exists ((A Address))
                (<= (ind C A) (old-bal A) )
            )
            (<= (count C) old-sum )
        )
    )
)
(assert
    (forall ((C Coin))
        (=
            (exists ((A Address))
                (<= (ind C A) (new-bal A))
            )
            (<= (count C) new-sum)
        )
    )
)

;                                I2''
(assert
    (forall ((A Address)(B Address)(C Coin))
        (=>
            (and
                (<= (ind C A) (old-bal A) )
                (<= (ind C B) (old-bal B) )
            )
            (= A B)
        )
    )
)
(assert
    (forall ((A Address)(B Address)(C Coin))
        (=>
            (and
                (<= (ind C A) (new-bal A) )
                (<= (ind C B) (new-bal B) )
            )
            (= A B)
        )
    )
)

; #########################################################################################
; ############################  transitions and negated impact  ###########################
; #########################################################################################

;                               double Transition
(assert
    (and
        (= (new-bal a0) (+ (old-bal a0) 3))
        (= (old-bal a1) (+ (new-bal a1) 3))
        (forall ((A Address ))
            (=>
                (and (distinct A a0) (distinct A a1))
                (= (old-bal A) (new-bal A))
            )
        )
    )
)

;                                Negated Impact
(assert
    (distinct  old-sum new-sum)
)

(check-sat)
;(get-model)
;(get-info :all-statistics)
