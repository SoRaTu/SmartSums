(set-logic UFDT)

(declare-sort Coin 0 )
(declare-sort Address 0)
(declare-sort Nat 0)

(declare-fun old-sum () Nat)
(declare-fun new-sum () Nat)
(declare-fun a0 () Address)

(declare-fun zero () Nat)
(declare-fun s (Nat) Nat)
(declare-fun leq (Nat Nat) Bool)

(declare-fun old-bal (Address) Nat)
(declare-fun new-bal (Address) Nat)
(declare-fun count (Coin) Nat)
(declare-fun ind (Coin Address) Nat)

; #########################################################################################
; ################################  naturals axioms  ######################################
; #########################################################################################

(assert
    (forall ((X Nat) (Y Nat))
        (=
            (and 
                (leq X Y)
                (leq Y X)
            )
            (= Y X)
        )
    )
)

(assert
    (forall ((X Nat)(Y Nat)) 
        (= 
            (leq (s X) Y)
            (and (leq X Y) (distinct X Y))
        )
    )
)

(assert
    (forall ((Y Nat)(X Nat))
        (=>
            (leq (s X) Y)
            (distinct Y zero)
        )
    )
)

(assert 
    (forall ((X Nat)(Y Nat))
        (=
            (leq (s Y) (s X))
            (leq Y X)
        )
    )
)

(assert
    (forall ((X Nat)(Y Nat)(Z Nat))
        (=>
            (and (leq X Y) (leq Y Z))
            (leq X Z)
        )
    )
)

(assert
    (forall ((X Nat)(Y Nat))
        (=
           (not (leq (s X) Y))
           (leq Y X)
        )
    )
)
; #########################################################################################
; ########################  axioms on sum and count  ######################################
; #########################################################################################

;                                count positive
(assert
    (forall ((C Coin))
        (distinct zero (count C))
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
    (or
        (= zero new-sum)
        (exists ((C Coin)) 
            (= (count C) new-sum)
        )
    )    
)
(assert 
    (or
        (= zero (s old-sum))
        (exists ((C Coin)) 
            (= (count C) (s old-sum))
        )
    )    
)


; #########################################################################################
; #########################  axioms on bal and ind ########################################
; #########################################################################################

;                                ind positive
(assert
    (forall ((C Coin)(A Address))
        (distinct zero (ind C A))
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
        (= zero (new-bal a0))
        (exists ((C Coin))
            (= (ind C a0) (new-bal a0) ) 
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
                (leq (ind C A) (old-bal A) )
            )
            (leq (count C) old-sum )
        )
    )
)
(assert
    (forall ((C Coin))
        (=
            (exists ((A Address))
                (leq (ind C A) (new-bal A))
            )
            (leq (count C) new-sum)
        )
    )
)


;                           coin only belongs to one address a.k.a only once ind leq bal
(assert
    (forall ((A Address)(B Address)(C Coin))
        (=>
            (and
                (leq (ind C A) (old-bal A) )
                (leq (ind C B) (old-bal B) )
            )
            (= A B)
        )
    )
)
(assert
    (forall ((A Address)(B Address)(C Coin))
        (=>
            (and
                (leq (ind C A) (new-bal A) )
                (leq (ind C B) (new-bal B) )
            )
            (= A B)
        )
    )
)


; #########################################################################################
; ############################  transition and negated impact  ###########################
; #########################################################################################


;                                Mint1
(assert
    (and
        (= (new-bal a0) (s (old-bal a0) ))
        (forall ((A Address ))
            (=>
                (distinct A a0)
                (= (old-bal A) (new-bal A))
            )
        )
    )
)

;                               negated Impact
(assert
    (distinct new-sum (s old-sum))
)


(check-sat)
;(get-model)
;(get-info :all-statistics)
