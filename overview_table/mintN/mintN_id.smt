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

; #########################################################################################
; ################################  naturals axioms  ######################################
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

(assert-theory
    (forall ((X Nat)(Y Nat)) 
        (= 
            (leq (s X) Y)
            (and (leq X Y) (distinct X Y))
        )
    )
)

(assert-theory
    (forall ((Y Nat)(X Nat))
        (=>
            (leq (s X) Y)
            (distinct Y zero)
        )
    )
)

(assert-theory
    (forall ((X Nat)(Y Nat))
        (=
            (leq (s Y) (s X))
            (leq Y X)
        )
    )
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
    (forall ((X Nat)(Y Nat))
        (=
           (not (leq (s X) Y))
           (leq Y X)
        )
    )
)


;axioms about add

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

; v  (combining add and s)
(assert-theory
    (forall ((A Nat)(N Nat))
        (=>
            (distinct N zero)
            (leq (s A) (add A N) )
        )
    )
)

(assert
    (distinct n zero)
)

(declare-fun null () Coin)
(declare-fun next (Coin) Coin)
(declare-fun count (Coin) Nat)
(declare-fun reachable (Coin Coin) Bool)
(declare-fun addr-next (Address Coin) Coin)
(declare-fun ind (Coin Address) Nat)
(declare-fun addr-reachable (Address Coin Coin) Bool)

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

; #########################################################################################
; ########################  linked lists for coins  #######################################
; #########################################################################################



(assert
    (= (count null) zero)
)

(assert
    (forall ((C Coin))
        (=>
            (distinct C null)
            (= (count C) (s (count (next C))))
        )
    )
)



(assert
    (forall ((C Coin))
        (reachable C C)
    )
)

(assert
    (forall ((C1 Coin) (C2 Coin))
        (=>
            (distinct C1 C2)
            (=
                (reachable C1 C2)
                (and
                    (distinct C1 null)
                    (reachable (next C1) C2)
                )
            )
        )
    )
)



(assert
    (forall ((A Address))
        (= (ind null A) zero)
    )
)

(assert
    (forall ((A Address) (C Coin))
        (=>
            (distinct C null)
            (= (ind C A) (s (ind (addr-next A C) A)))
        )
    )
)



(assert
    (forall ((A Address) (C Coin))
        (addr-reachable A C C)
    )
)

(assert
    (forall ((A Address) (C1 Coin) (C2 Coin))
        (=>
            (distinct C1 C2)
            (=
                (addr-reachable A C1 C2)
                (and
                    (distinct C1 null)
                    (addr-reachable A (addr-next A C1) C2)
                )
            )
        )
    )
)

; #########################################################################################
; ########################  axioms on sum and count  ######################################
; #########################################################################################

;                               only self-loop is null
(assert
    (forall ((C Coin))
        (=
            (= C (next C))
            (= C null)
        )
    )
)

;                               there's only one linked list
(assert
    (forall ((C1 Coin) (C2 Coin))
       (or
            (reachable C1 C2)
            (reachable C2 C1)
        )
    )
)

;                               {old,new}-sum match to some coin, i.e. surjectivity
(assert
    (exists ((C Coin))
        (=
            (count C)
            old-sum
        )
    )
)

(assert
    (exists ((C Coin))
        (=
            (count C)
            new-sum
        )
    )
)

; #########################################################################################
; #########################  axioms on bal and ind ########################################
; #########################################################################################

;                               only self-loop is null
(assert
    (forall ((A Address) (C Coin))
        (=
            (= C (addr-next A C))
            (= C null)
        )
    )
)

;                               there's only one linked list per address
(assert
    (forall ((A Address) (C1 Coin) (C2 Coin))
        (or
            (addr-reachable A C1 C2)
            (addr-reachable A C2 C1)
        )
    )
)

;                           {old,new}-bal match some coin-i.e. surjectivity
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
        (or
            (= C null)
            (=>
                (and
                    (leq (ind C A) (old-bal A) )
                    (leq (ind C B) (old-bal B) )
                )
                (= A B)
            )
        )
    )
)
(assert
    (forall ((A Address)(B Address)(C Coin))
        (or
            (= C null)
            (=>
                (and
                    (leq (ind C A) (new-bal A) )
                    (leq (ind C B) (new-bal B) )
                )
                (= A B)
            )
        )
    )
)


; #########################################################################################
; ############################  transition and negated impact  ###########################
; #########################################################################################


;                                MintN
(assert
    (and
        (= (new-bal a0) (add (old-bal a0) n))
        (forall ((A Address ))
            (=>
                (distinct A a0)
                (= (old-bal A) (new-bal A))
            )
        )
    )
)

;                             Inductive property
(assert
    (forall ((A Address) (C Coin) (D Coin))
        (=
            (addr-reachable A D C)
            (leq (ind C A) (ind D A))
        )
    )
)

;                               negated Impact
(assert-not
    (= new-sum (add old-sum n ))
)

; Lemma
(assert
    (=>
        (and
            (leq (s old-sum) new-sum )
            (leq (s (add old-sum (old-bal a0)) )   (add old-sum (add (old-bal a0) n) ) )
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
        (= new-sum (add old-sum n))
    )

)


(check-sat)
;(get-model)
;(get-info :all-statistics)
