(set-logic UFLIA)

(declare-sort Coin 0 )
(declare-sort Address 0)
(declare-fun old-sum () Int)
(declare-fun new-sum () Int)
(declare-fun a0 () Address)
(declare-fun old-total () Int) ;NEW
(declare-fun new-total () Int) ;NEW

(declare-fun old-bal (Address) Int)
(declare-fun new-bal (Address) Int)
(declare-fun count (Coin) Int)
(declare-fun ind (Coin Address) Int)



; #########################################################################################
; ########################  axioms on sum and count #######################################
; #########################################################################################

;                             sum non-negative
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


;                                count surjective
(assert 
    (or
        (= 0 new-sum)
        (exists ((C Coin)) 
            (= (count C) new-sum)
        )
    )    
)
(assert 
    (or
        (= 0 (+ old-sum 1))
        (exists ((C Coin)) 
            (= (count C) (+ old-sum 1))
        )
    )    
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


;                                ind(A,.) surjective
(assert
    (or
        (= 0 (new-bal a0))
        (exists ((C Coin))
            (= (ind C a0) (new-bal a0) ) 
        )
    )
)


; #########################################################################################
; ###############################  axioms between sum and bal #############################
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


;                         coin only belongs to one address a.k.a only once ind leq bal
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
; ############################  transition and negated impact  ############################
; #########################################################################################

;                                Mint1
(assert
    (and
        (= (new-bal a0) (+ (old-bal a0) 1))
        (forall ((A Address ))
            (=>
                (distinct A a0)
                (= (old-bal A) (new-bal A))
            )
        )
    )
)


;                               Impact on total 
(assert
    (= (+ old-total 1) new-total) 
)

; #########################################################################################
; #####################################  invariants  ######################################
; #########################################################################################

;                              pre-invariant 
(assert
    (= old-sum old-total)   
)

;                              negated post-invariant  
(assert
    (distinct new-sum new-total)    
)


(check-sat)
;(get-model)
;(get-info :all-statistics)
