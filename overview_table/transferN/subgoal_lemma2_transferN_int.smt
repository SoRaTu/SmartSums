(set-logic UFLIA)

(declare-sort Coin 0 )
(declare-sort Address 0)

(declare-fun old-sum () Int)
(declare-fun new-sum () Int)
(declare-fun a0 () Address)
(declare-fun a1 () Address)
(declare-fun c1 () Coin)

(declare-fun n () Int)

(declare-fun old-bal (Address) Int)
(declare-fun new-bal (Address) Int)
(declare-fun count (Coin) Int)
(declare-fun ind (Coin Address) Int)

(assert
    (> n 0)
)


;                                sum non-negative
(assert
    (<= 0 old-sum)
)
(assert
    (<= 0 new-sum)
)

;                                bal non-negative
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

;                                "surjectivity"
(assert
    (= (count c1) old-sum )
)


(assert
    (exists ((D Coin))
        (=
            (+  (ind c1 a0)  (old-bal a1) )
            (+  (ind D a1)  (new-bal a0) )
        )
    )
)


;                                  injectivity
(assert
    (forall ((C Coin) (D Coin))
        (=>
            (= (ind C a0) (ind D a0))
            (= C D)
        )
    )
)

;axiom2
(assert
 (=>
    (forall ((C Coin))
        (=>
            (and
                (<= (+ (old-bal a1) 1) (ind C a1) )
                (<= (ind C a1) (+ (old-bal a1) n) )
            )
            (and
                (<= (+ (new-bal a0) 1) (ind C a0) )
                (<= (ind C a0) (+ (new-bal a0) n) )
            )
        )
    )
    (forall ((C Coin))
        (=>
            (and
                (<= (+ (old-bal a1) 1) (ind C a1) )
                (<= (ind C a1) (+ (old-bal a1) n) )
            )
            (= 
                (+ (ind C a0) (old-bal a1))
                (+ (ind C a1) (new-bal a0))
            )
        )
    )
 )
)


;                sum-logic:
;  every active coin assigned to precisely one address a.k.a. ind leq bal iff count leq sum
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

;                                  tfN
(assert
    (and
        (= (old-bal a0) (+ (new-bal a0) n) )
        (= (new-bal a1) (+ (old-bal a1) n) )
        (forall ((A Address ))
            (=>
                (and (distinct A a0) (distinct A a1) )
                (= (old-bal A) (new-bal A))
            )
        )
    )
)



; ############################################################################################
; ################################### Lemma 2: assumptions ###################################
; ############################################################################################

(assert
    (forall ((C Coin))
        (=>
            (and
                (<= (+ (old-bal a1) 1) (ind C a1) )
                (<= (ind C a1) (+ (old-bal a1) n) )
            )                
            (and
                (<= (+ (new-bal a0) 1) (ind C a0) )
                (<= (ind C a0) (+ (new-bal a0) n) )
            )
        )
    )
)

(assert 
    (<= new-sum old-sum)
)

; ############################################################################################
; ####################################### proof goal #########################################
; ############################################################################################

; proven as intermediate goal in 81 sec NEEDED (7,6,10)
(assert
(not
    (or
        (= old-sum new-sum)
        (exists ((D Coin))
            (and
                (=
                    (+  (ind c1 a0)  (old-bal a1) )
                    (+  (ind D a1)  (new-bal a0) )
                )
                (<= (+ (old-bal a1) 1) (ind D a1) )
                (<= (ind D a1)  (+ (old-bal a1) n)  )
                (=
                    (+  (ind D a1)  (new-bal a0) )
                    (+  (ind D a0)  (old-bal a1) )
                )
            )
        )
    )
))

(check-sat)
;(get-model)
;(get-info :all-statistics)