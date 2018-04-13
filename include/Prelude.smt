; disable model-based quantifier instantiation (avoid loops)
(set-option :smt.mbqi false)

; For polymorphic types:
(declare-sort TVar)

; Pair type:
(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

; For functional types:
(declare-datatypes (T1 T2) ((Func (mk-func (argument T1) (result T2)))))

; Ordering type:
(declare-datatypes () ((Ordering LT EQ GT)))

