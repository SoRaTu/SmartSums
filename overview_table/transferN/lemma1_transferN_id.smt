(set-logic UFDT)

(declare-sort Coin 0 )
(declare-sort Address 0)
(declare-sort Nat 0)

(declare-fun old-sum () Nat)
(declare-fun new-sum () Nat)
(declare-fun a0 () Address)
(declare-fun a1 () Address)
(declare-fun c0 () Coin)

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
; #########################################  axioms  ######################################
; #########################################################################################

(assert-theory
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

; i
(assert-theory
   (forall ((A Nat)(B Nat)(N Nat))
        (=
            (leq A B )
            (leq (add A N ) (add B N))
        )
    )
)

; ii
(assert-theory
    (forall ((A Nat)(B Nat))
        (=   (add (s A) B)   (s (add A B))  )
    )
)
; iii
(assert-theory
    (forall ((A Nat)(B Nat))
        (= (add A B ) (add B A ))
    )
)

; iv
(assert-theory
    (forall ((A Nat)(B Nat)(C Nat ))
        (= (add A (add B C))  (add (add A B) C)  )
    )
)

(assert
    (distinct n zero)
)

(assert-theory
    (forall ((X Nat)(Y Nat)(Z Nat))
        (=>
            (and (leq X Y) (leq Y Z))
            (leq X Z)
        )
    )
)

(assert-theory
    (forall ((A Nat)(N Nat))
        (leq A (add A N) )
    )
)


;totality axiom
(assert-theory
    (forall  ((C Coin))
        (or 
            (leq (ind C a1) (old-bal a1) )  
            (leq (s (old-bal a1)) (ind C a1) ) 
        )
    )
)

;                                "surjectivity"
(assert 
    (= (count c0) new-sum)  
)

(assert
    (forall ((A Address))
        (exists ((C Coin))
            (=
                (ind C A)
                (old-bal A)
            )
        )
    )
)
(assert
    (forall ((A Address))
        (exists ((C Coin))
            (=
                (ind C A)
                (new-bal A)
            )
        )
    )
)

;                                  injectivity
(assert
    (forall ((C Coin) (D Coin))
        (=>
            (= (ind C a1) (ind D a1))
            (= C D)
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

;                sum-logic:
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

;                                  tfN
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



; ############################################################################################
; ################################### Lemma 2: assumptions ###################################
; ############################################################################################

(assert
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

(assert 
    (leq old-sum new-sum)
)

; ############################################################################################
; ####################################### proof goal #########################################
; ############################################################################################

; proven as subgoal in 98 sec NEEDED
(assert
    (or
        (= old-sum new-sum)
        (exists ((D Coin))
            (and
                (=
                    (add  (ind c0 a1)  (new-bal a0) )
                    (add  (ind D a0)  (old-bal a1) )
                )
                (leq (s (new-bal a0) ) (ind D a0) )
                (leq (ind D a0)  (add (new-bal a0) n)  )
                (=
                    (add  (ind D a1)  (new-bal a0) )
                    (add  (ind D a0)  (old-bal a1) )
                )
            )
        )
    )
)

(assert-not ;(7,6,10)
    (= old-sum new-sum)
)

(check-sat)
;(get-model)
;(get-info :all-statistics)
