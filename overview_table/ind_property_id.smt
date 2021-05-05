(set-logic UFDT)

(declare-sort Coin 0 )
(declare-sort Address 0)
;(declare-sort Nat 0) ; only for smt solver, to be removed for Vampire
(declare-datatypes ((Nat 0)) (      ;for Vampire
    ((s (predecessor Nat)) (zero))  ; for Vampire
))                                   ; for Vampire

;(declare-fun zero () Nat ) ; only for smt solver, to be removed for Vampire
;(declare-fun s (Nat) Nat) ;only for smt solver, to be removed for Vampire
(declare-fun leq (Nat Nat) Bool)



; #########################################################################################
; ################################  naturals axioms  ######################################
; #########################################################################################

(assert-theory ;all the -theory tags have to be commented out for smt solver
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

; #########################################################################################
; ########################  definitions of ind and addr-reachable  ########################
; #########################################################################################

(declare-fun null () Coin)

(declare-fun addr-next (Address Coin) Coin)

(declare-fun ind (Coin Address) Nat)

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

(declare-fun addr-reachable (Address Coin Coin) Bool)

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

;###########################################################################################
;##################### Property to be ensured ##############################################
;###########################################################################################

(declare-fun helper (Nat) Bool)
(assert
    (forall ((N Nat))
        (=
            (helper N)
            (forall ((A Address)(B Coin)(C Coin))
                (=>
                    (= N (ind C A))
                    (=>
                        (addr-reachable A C B)
                        (leq (ind B A )  (ind C A))
                    )
                )
            )
        )
    )
)
(assert-not
 (forall ((N Nat)) (helper N)) 
)

; the exact call is:
 ;./vampire --input_syntax smtlib2  ind_property_id.smt --forced_options "ind=struct:thsq=on:thsqd=10:thsqc=10:thsqr=20,1:av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off:sa=discount:s=1010:awr=3"  

(check-sat)
;(get-model)
;(get-info :all-statistics)
