(set-logic UFLIA)

(declare-sort Coin 0 )
(declare-sort Address 0)

(declare-fun old-sum () Int)
(declare-fun new-sum () Int)
(declare-fun a0 () Address)

(declare-fun n () Int)

(declare-fun old-bal (Address) Int)
(declare-fun new-bal (Address) Int)
(declare-fun count (Coin) Int)
(declare-fun ind (Coin Address) Int)


;                                "surjectivity"
(assert 
        (exists ((C Coin)) 
            (= (count C) new-sum)
        )   
)

(assert 
        (exists ((C Coin)) 
            (= (ind C a0) (+ (old-bal a0) n))
        )   
)


;axiom
(assert
 (=>
    (forall ((C Coin))
        (=
            (and
                (<= (+ (old-bal a0) 1) (ind C a0) )
                (<= (ind C a0) (+ (old-bal a0) n) )
            )
            (and
                (<= (+ old-sum 1) (count C))
                (<= (count C) new-sum)
            )
        )
    )
    (forall ((C Coin))
        (=>
            (and
                (<= (+ (old-bal a0) 1) (ind C a0) )
                (<= (ind C a0) (+ (old-bal a0) n) )
            )
            (= 
                (+ (ind C a0) old-sum)
                (+ (count C) (old-bal a0))
            )
        )
    )
 )
)




; ############################################################################################
; ################################### Lemma 1: assumptions ###################################
; ############################################################################################


(assert
    (forall ((C Coin))
        (=
            (and
                (<= (+ (old-bal a0) 1) (ind C a0) )
                (<= (ind C a0) (+ (old-bal a0) n) )
            )
            (and
                (<= (+ old-sum 1) (count C))
                (<= (count C) new-sum)
            )
        )
    )
)

; follows from: leq (s (old-bal a0)) (new-bal a0)
(assert
    (<= (+  old-sum 1)   new-sum )
)

;follows from: n>0
(assert
    (<= (+ (+ old-sum (old-bal a0)) 1)   (+ old-sum (+ (old-bal a0) n) ) )
)

; ############################################################################################
; ####################################### proof goal #########################################
; ############################################################################################

(assert
    (distinct (+ old-sum n) new-sum )
)

(check-sat)
;(get-model)
;(get-info :all-statistics)
