(set-logic UFLIA)

(declare-sort Coin 0 )
(declare-sort Address 0)

(declare-fun old-sum () Int)
(declare-fun new-sum () Int)
(declare-fun a0 () Address)
(declare-fun a1 () Address)

(declare-fun c0 () Coin)
(declare-fun c1 () Coin)

(declare-fun n () Int)

(declare-fun old-bal (Address) Int)
(declare-fun new-bal (Address) Int)
(declare-fun count (Coin) Int)
(declare-fun ind (Coin Address) Int)

(assert
    (> n 0)
)

;axiom1
(assert
    (=>
        (forall ((C Coin))
            (=>
                (and
                    (<= (+ (new-bal a0) 1) (ind C a0) )
                    (<= (ind C a0) (+ (new-bal a0) n) )
                )
                (and
                    (<= (+ (old-bal a1) 1) (ind C a1) )
                    (<= (ind C a1) (+ (old-bal a1) n) )
                )
            )
        )
        (forall ((C Coin))
            (=>
                (and
                    (<= (+ (new-bal a0) 1) (ind C a0) )
                    (<= (ind C a0) (+ (new-bal a0) n) )
                )
                (= 
                    (+ (ind C a0) (old-bal a1))
                    (+ (ind C a1) (new-bal a0))
                )
            )
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

; #########################################################################################
; ########################  axioms on sum and count  ######################################
; #########################################################################################

;                                sum non-negative
(assert
    (<= 0 old-sum)
)
(assert
    (<= 0 new-sum)
)

;                                count positive
(assert
    (forall ((C Coin))
        (< 0 (count C))
    )
)

;                                count injective
(assert
    (forall ((C Coin) (D Coin))
        (=>
            (= (count C) (count D))
            (= C D)
        )
    )
)

;                                count "surjective"
(assert 
    (= (count c0) new-sum)  
)
(assert 
    (= (count c1) old-sum) 
)

; #########################################################################################
; #########################  axioms on bal and ind ########################################
; #########################################################################################

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

;                                ind positive
(assert
    (forall ((C Coin)(A Address))
        (< 0 (ind C A))
    )
)

;                                ind(A,.) injective
(assert
    (forall ((C Coin) (D Coin) (A Address))
        (=>
            (= (ind C A) (ind D A))
            (= C D)
        )
    )
)

;                                ind(A,.) "surjective"

(assert
    (exists ((D Coin))
        (=
            (+  (ind c0 a1)  (new-bal a0) )
            (+  (ind D a0)  (old-bal a1) )
        )
    )
)

(assert
    (exists ((D Coin))
        (=
            (+  (ind c1 a0)  (old-bal a1) )
            (+  (ind D a1)  (new-bal a0) )
        )
    )
)

; #########################################################################################
; ###############################  axioms between sum and bal  ############################
; #########################################################################################

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


;                           coin only belongs to one address a.k.a only once ind leq bal
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
; ############################  transition and negated impact  ###########################
; #########################################################################################


;                                TransferN
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

;                               negated Impact
(assert
   (distinct old-sum new-sum)
)


; Lemma1
(assert
    (=>
        (and
            (<= old-sum new-sum )
            (forall ((C Coin))
                (=>
                    (and
                        (<= (+ (new-bal a0) 1) (ind C a0) )
                        (<= (ind C a0) (+ (new-bal a0) n) )
                    )
                    (and
                        (<= (+ (old-bal a1) 1) (ind C a1) )
                        (<= (ind C a1) (+ (old-bal a1) n) )
                    )
                )
            )
        )
        (= new-sum old-sum)
    )
)

;Lemma2
(assert
    (=>
        (and
            (<= new-sum old-sum )
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
        (= new-sum old-sum)
    )
)

(check-sat)
;(get-model)
;(get-info :all-statistics)
