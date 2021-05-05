(set-logic UFDT)

(declare-sort Coin 0 )
(declare-sort Address 0)
(declare-sort Nat 0)

(declare-fun old-sum () Nat)
(declare-fun new-sum () Nat)
(declare-fun a0 () Address)
(declare-fun a1 () Address)

(declare-fun c0 () Coin)
(declare-fun c1 () Coin)

(declare-fun zero () Nat)
(declare-fun s (Nat) Nat)
(declare-fun leq (Nat Nat) Bool)
(declare-fun add (Nat Nat) Nat)
(declare-fun n () Nat)

(declare-fun old-bal (Address) Nat)
(declare-fun new-bal (Address) Nat)
(declare-fun count (Coin) Nat)
(declare-fun ind (Coin Address) Nat)

; #########################################################################################
; ################################  naturals axioms  ######################################
; #########################################################################################

(assert;-theory
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

(assert;-theory
    (forall ((X Nat)(Y Nat)) 
        (= 
            (leq (s X) Y)
            (and (leq X Y) (distinct X Y))
        )
    )
)

(assert;-theory
    (forall ((Y Nat)(X Nat))
        (=>
            (leq (s X) Y)
            (distinct Y zero)
        )
    )
)

(assert;-theory
    (forall ((X Nat)(Y Nat))
        (=
            (leq (s Y) (s X))
            (leq Y X)
        )
    )
)

(assert;-theory
    (forall ((X Nat)(Y Nat)(Z Nat))
        (=>
            (and (leq X Y) (leq Y Z))
            (leq X Z)
        )
    )
)

(assert;-theory
    (forall ((X Nat)(Y Nat))
        (=
           (not (leq (s X) Y))
           (leq Y X)
        )
    )
)

;axioms about add

; i
(assert;-theory
   (forall ((A Nat)(B Nat)(N Nat))
        (=
            (leq A B )
            (leq (add A N ) (add B N))
        )
    )
)

; ii
(assert;-theory
    (forall ((A Nat)(B Nat))
        (=   (add (s A) B)   (s (add A B))  )
    )
)
; iii
(assert;-theory
    (forall ((A Nat)(B Nat))
        (= (add A B ) (add B A ))
    )
)

; iv
(assert;-theory
    (forall ((A Nat)(B Nat)(C Nat ))
        (= (add A (add B C))  (add (add A B) C)  )
    )
)

; v  (combining add and s)
(assert;-theory
    (forall ((A Nat)(N Nat))
        (=>
            (distinct N zero)
            (leq (s A) (add A N) )
        )
    )
)

;vi
(assert;-theory
    (forall ((A Nat)(N Nat))
        (leq A (add A N) )
    )
)

(assert
    (distinct n zero)
)


;totality axioms
(assert
    (or (leq old-sum new-sum)  (leq new-sum old-sum)  )
)
(assert;-theory
    (forall  ((C Coin))
        (or 
            (leq (ind C a1) (old-bal a1) )  
            (leq (s (old-bal a1)) (ind C a1) ) 
        )
    )
)
(assert;-theory
    (forall  ((C Coin))
        (or 
            (leq (ind C a0) (new-bal a0) )  
            (leq (s (new-bal a0)) (ind C a0) ) 
        )
    )
)

;axiom1
(assert
    (=>
        (forall ((C Coin))
            (=>
                (and
                    (leq (s (new-bal a0)) (ind C a0) )
                    (leq (ind C a0) (add (new-bal a0) n) )
                )
                (and
                    (leq (s (old-bal a1)) (ind C a1) )
                    (leq (ind C a1) (add (old-bal a1) n) )
                )
            )
        )
        (forall ((C Coin))
            (=>
                (and
                    (leq (s (new-bal a0)) (ind C a0) )
                    (leq (ind C a0) (add (new-bal a0) n) )
                )
                (= 
                    (add (ind C a0) (old-bal a1))
                    (add (ind C a1) (new-bal a0))
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
                (leq (s (old-bal a1)) (ind C a1) )
                (leq (ind C a1) (add (old-bal a1) n) )
            )
            (and
                (leq (s (new-bal a0)) (ind C a0) )
                (leq (ind C a0) (add (new-bal a0) n) )
            )
        )
    )
    (forall ((C Coin))
        (=>
            (and
                (leq (s (old-bal a1)) (ind C a1) )
                (leq (ind C a1) (add (old-bal a1) n) )
            )
            (= 
                (add (ind C a0) (old-bal a1))
                (add (ind C a1) (new-bal a0))
            )
        )
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
    (= (count c0) new-sum)  
)
(assert 
    (= (count c1) old-sum) 
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

;                                ind(A,.) "surjective"

(assert
    (exists ((D Coin))
        (=
            (add  (ind c0 a1)  (new-bal a0) )
            (add  (ind D a0)  (old-bal a1) )
        )
    )
)

(assert
    (exists ((D Coin))
        (=
            (add  (ind c1 a0)  (old-bal a1) )
            (add  (ind D a1)  (new-bal a0) )
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


;                                TransferN
(assert
    (and
        (= (old-bal a0) (add (new-bal a0) n) )
        (= (new-bal a1) (add (old-bal a1) n) )
        (forall ((A Address ))
            (=>
                (and (distinct A a0) (distinct A a1) )
                (= (old-bal A) (new-bal A))
            )
        )
    )
)

;                               negated Impact
(assert;-not
   (distinct old-sum new-sum)
)


; Lemma1
(assert
    (=>
        (and
            (leq old-sum new-sum )
            (forall ((C Coin))
                (=>
                    (and
                        (leq (s (new-bal a0)) (ind C a0) )
                        (leq (ind C a0) (add (new-bal a0) n) )
                    )
                    (and
                        (leq (s (old-bal a1)) (ind C a1) )
                        (leq (ind C a1) (add (old-bal a1) n) )
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
            (leq new-sum old-sum )
            (forall ((C Coin))
                (=>
                    (and
                        (leq (s (old-bal a1)) (ind C a1) )
                        (leq (ind C a1) (add (old-bal a1) n) )
                    )
                    (and
                        (leq (s (new-bal a0)) (ind C a0) )
                        (leq (ind C a0) (add (new-bal a0) n) )
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
