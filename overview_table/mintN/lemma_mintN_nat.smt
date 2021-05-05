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
(declare-fun add (Nat Nat) Nat)
(declare-fun n () Nat)

(declare-fun old-bal (Address) Nat)
(declare-fun new-bal (Address) Nat)
(declare-fun count (Coin) Nat)
(declare-fun ind (Coin Address) Nat)

; #########################################################################################
; #########################################  axioms  ######################################
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


;                                "surjectivity"
(assert 
        (exists ((C Coin)) 
            (= (count C) new-sum)
        )   
)

(assert 
        (exists ((C Coin)) 
            (= (ind C a0) (add (old-bal a0) n))
        )   
)


;axiom2
(assert
 (=>
    (forall ((C Coin))
        (=
            (and
                (leq (s (old-bal a0)) (ind C a0) )
                (leq (ind C a0) (add (old-bal a0) n) )
            )
            (and
                (leq (s old-sum) (count C))
                (leq (count C) new-sum)
            )
        )
    )
    (forall ((C Coin))
        (=>
            (and
                (leq (s (old-bal a0)) (ind C a0) )
                (leq (ind C a0) (add (old-bal a0) n) )
            )
            (= 
                (add (ind C a0) old-sum)
                (add (count C) (old-bal a0))
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
                (leq (s (old-bal a0)) (ind C a0) )
                (leq (ind C a0) (add (old-bal a0) n) )
            )
            (and
                (leq (s old-sum) (count C))
                (leq (count C) new-sum)
            )
        )
    )
)

; follows from: leq (s (old-bal a0)) (new-bal a0)
(assert
    (leq (s  old-sum)   new-sum )
)

;follows from: n>0
(assert
    (leq (s (add old-sum (old-bal a0)) )   (add old-sum (add (old-bal a0) n) ) )
)

; ############################################################################################
; ####################################### proof goal #########################################
; ############################################################################################

(assert;-not
    (distinct (add old-sum n) new-sum )
)

(check-sat)
;(get-model)
;(get-info :all-statistics)
