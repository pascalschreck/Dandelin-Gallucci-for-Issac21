# Dandelin-Gallucci-for-Issac21

This is a short explanation of the Coq directory of this repository.
There are six files.
Three statements which have suffix "stat" :

* Pappus2DG_R_exists.stat, existence of point R (see below)
* Pappus2DG_alt2_simpl.stat, Pappus => Dandelin-Gallucci
* dg2pappusAlt2.stat, Dandelin-Gallucci => Pappus

Three Coq files with suffix "v". Each Coq file contains a preamble  where tactics and basic lemmas are defined, and a part which is automatically produced by our prover.
The names of that files correspond to their statements. Including the preamble allows to directly test these proofs with Coqide for instance.

## reproduction of the proofs 

Go to https://github.com/pascalschreck/MatroidIncidenceProver
Compile the project (in DevC subdirectory : make init and then make), the executable file is in subdirectory bin and its name is main.

Now with "main" directory supposed to be in PATH variable :
main -s <name of the statement file (with .stat)\> 
produces a file <name of the statement\>.v and some other files (it may take a long time)
You just have to add the preamble instead of the first line.

## Proof of Pappus implies DG
There are three steps

* building an instance of Pappus : this is done by hand. It is hard to discover a particular instance in the figure and how tu use it. Here points X, Y and Z are constructed following the geometric proof given int the paper.
* proving that the lines YM and ZN are different and coplanar, hence their intersection consists in one point. It is called R in the geometric proof.
* proving that lines h and d are coplanar.

### instance of Pappus
done by hand (this is the hypothesis)

### existence of R
This a proof that is automatically given by our prover.
Statement :

```
context
    dimension 3
    layers 1
endofcontext
layer donnees
    points
         Oo A B C Ap Bp Cp X Y Z M N P Q 
    hypotheses
        Oo A : 2
        Oo B : 2
        Oo C : 2
        A B : 2
        A C : 2
        B C : 2
        Oo Ap : 2
        Oo Bp : 2
        Oo Cp : 2
        Ap Bp : 2
        Ap Cp : 2
        Bp Cp : 2
        Oo A B C : 2                	# a
        Ap M Q : 2              	# b
        Oo A B C Ap M Q : 4      # a and b are not coplanar
        Bp P N : 2                	# c
        Oo A B C Bp P N : 4       # a and c are not coplanar
        Ap M Q Bp P N : 4      	# b and c are not coplanar
        Oo Ap Bp Cp : 2             # e
        Oo A Ap : 3                 	# a and e are different
        A M P : 2                 	# f
        Oo Ap Bp Cp A M P : 4     # e and f are not coplanar
        B Q N : 2                	 # g
        Oo Ap Bp Cp B Q N : 4     # e and g are not coplanar
        A M P B Q N : 4         	# f and g are not coplanar
        X A Bp : 2                  	# 1st Pappus point
        X Ap B : 2
        Y A Cp : 2                  	# 2nd Pappus point
        Y Ap C : 2
        Z C Bp : 2                  	# 3rd Pappus point
        Z Cp B : 2
        X Y Z : 2                  	 # Pappus colinearity
    conclusion
        Y M Z N : 3             	#  lines YM and ZN are coplanar thus they meet 
endoflayer 
conclusion
    Y M Z N : 3            		# lines YM and ZN are coplanar thus they meet
end 

```
Proof in Coq (see the Pappus2DG_R_exists_with_preamb.v). Here is the final Lemma of that file (this Lemma  _is_ the theorem we want to prove, previous Lemmas of the file are used in this proof) :


```
Lemma LYZMN : 
forall Oo A B C Ap Bp Cp X Y Z M N P Q ,
rk(Oo :: A ::  nil) = 2 -> 
rk(Oo :: B ::  nil) = 2 -> 
rk(A :: B ::  nil) = 2 ->
rk(Oo :: C ::  nil) = 2 -> 
rk(A :: C ::  nil) = 2 -> 
rk(B :: C ::  nil) = 2 ->
rk(Oo :: A :: B :: C ::  nil) = 2 -> 
rk(Oo :: Ap ::  nil) = 2 -> 
rk(Oo :: A :: Ap ::  nil) = 3 ->
rk(Oo :: Bp ::  nil) = 2 -> 
rk(Ap :: Bp ::  nil) = 2 -> 
rk(Oo :: Cp ::  nil) = 2 ->
rk(Ap :: Cp ::  nil) = 2 -> 
rk(Bp :: Cp ::  nil) = 2 -> 
rk(Oo :: Ap :: Bp :: Cp ::  nil) = 2 ->
rk(B :: Ap :: X ::  nil) = 2 -> 
rk(A :: Bp :: X ::  nil) = 2 -> 
rk(C :: Ap :: Y ::  nil) = 2 ->
rk(A :: Cp :: Y ::  nil) = 2 -> 
rk(C :: Bp :: Z ::  nil) = 2 -> 
rk(B :: Cp :: Z ::  nil) = 2 ->
rk(X :: Y :: Z ::  nil) = 2 -> 
rk(A :: M :: P ::  nil) = 2 -> 
rk(Oo :: A :: Ap :: Bp :: Cp :: M :: P ::  nil) = 4 ->
rk(Bp :: N :: P ::  nil) = 2 -> 
rk(Oo :: A :: B :: C :: Bp :: N :: P ::  nil) = 4 -> 
rk(Ap :: M :: Q ::  nil) = 2 ->
rk(Oo :: A :: B :: C :: Ap :: M :: Q ::  nil) = 4 -> 
rk(B :: N :: Q ::  nil) = 2 -> 
rk(Oo :: B :: Ap :: Bp :: Cp :: N :: Q ::  nil) = 4 ->
rk(A :: B :: M :: N :: P :: Q ::  nil) = 4 -> 
rk(Ap :: Bp :: M :: N :: P :: Q ::  nil) = 4 
->
rk(Y :: Z :: M :: N ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp X Y Z M N P Q 
HOoAeq HOoBeq HABeq HOoCeq HACeq HBCeq HOoABCeq HOoApeq HOoAApeq HOoBpeq
HApBpeq HOoCpeq HApCpeq HBpCpeq HOoApBpCpeq HBApXeq HABpXeq HCApYeq HACpYeq HCBpZeq
HBCpZeq HXYZeq HAMPeq HOoAApBpCpMPeq HBpNPeq HOoABCBpNPeq HApMQeq HOoABCApMQeq HBNQeq HOoBApBpCpNQeq
HABMNPQeq HApBpMNPQeq .


assert(HYZMNm2 : rk(Y :: Z :: M :: N :: nil) >= 2).
{
	try assert(HOoAApYeq : rk(Oo :: A :: Ap :: Y :: nil) = 3) by (apply LOoAApY with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (P := P) (Q := Q) ;try assumption).
	assert(HOoAApYMtmp : rk(Oo :: A :: Ap :: Y :: nil) <= 3) by (solve_hyps_max HOoAApYeq HOoAApYM3).
	try assert(HOoAApYZMNeq : rk(Oo :: A :: Ap :: Y :: Z :: M :: N :: nil) = 4) by (apply LOoAApYZMN with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (P := P) (Q := Q) ;try assumption).
	assert(HOoAApYZMNmtmp : rk(Oo :: A :: Ap :: Y :: Z :: M :: N :: nil) >= 4) by (solve_hyps_min HOoAApYZMNeq HOoAApYZMNm4).
	try assert(HYeq : rk(Y :: nil) = 1) by (apply LY with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (P := P) (Q := Q) ;try assumption).
	assert(HYmtmp : rk(Y :: nil) >= 1) by (solve_hyps_min HYeq HYm1).
	assert(Hincl : incl (Y :: nil) (list_inter (Oo :: A :: Ap :: Y :: nil) (Y :: Z :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: Ap :: Y :: Z :: M :: N :: nil) (Oo :: A :: Ap :: Y :: Y :: Z :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: Ap :: Y :: Y :: Z :: M :: N :: nil) ((Oo :: A :: Ap :: Y :: nil) ++ (Y :: Z :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoAApYZMNmtmp;try rewrite HT2 in HOoAApYZMNmtmp.
	assert(HT := rule_4 (Oo :: A :: Ap :: Y :: nil) (Y :: Z :: M :: N :: nil) (Y :: nil) 4 1 3 HOoAApYZMNmtmp HYmtmp HOoAApYMtmp Hincl); apply HT.
}

assert(HYZMNm3 : rk(Y :: Z :: M :: N :: nil) >= 3).
{
	try assert(HCBpZeq : rk(C :: Bp :: Z :: nil) = 2) by (apply LCBpZ with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (P := P) (Q := Q) ;try assumption).
	assert(HCBpZMtmp : rk(C :: Bp :: Z :: nil) <= 2) by (solve_hyps_max HCBpZeq HCBpZM2).
	try assert(HCBpYZMNeq : rk(C :: Bp :: Y :: Z :: M :: N :: nil) = 4) by (apply LCBpYZMN with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (P := P) (Q := Q) ;try assumption).
	assert(HCBpYZMNmtmp : rk(C :: Bp :: Y :: Z :: M :: N :: nil) >= 4) by (solve_hyps_min HCBpYZMNeq HCBpYZMNm4).
	try assert(HZeq : rk(Z :: nil) = 1) by (apply LZ with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (P := P) (Q := Q) ;try assumption).
	assert(HZmtmp : rk(Z :: nil) >= 1) by (solve_hyps_min HZeq HZm1).
	assert(Hincl : incl (Z :: nil) (list_inter (C :: Bp :: Z :: nil) (Y :: Z :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Bp :: Y :: Z :: M :: N :: nil) (C :: Bp :: Z :: Y :: Z :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Bp :: Z :: Y :: Z :: M :: N :: nil) ((C :: Bp :: Z :: nil) ++ (Y :: Z :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCBpYZMNmtmp;try rewrite HT2 in HCBpYZMNmtmp.
	assert(HT := rule_4 (C :: Bp :: Z :: nil) (Y :: Z :: M :: N :: nil) (Z :: nil) 4 1 2 HCBpYZMNmtmp HZmtmp HCBpZMtmp Hincl); apply HT.
}
try clear HCBpZM1. try clear HCBpZM2. try clear HCBpZM3. try clear HCBpZm4. try clear HCBpZm3. try clear HCBpZm2. try clear HCBpZm1. try clear HZM1. try clear HZM2. try clear HZM3. try clear HZm4. try clear HZm3. try clear HZm2. try clear HZm1. 

assert(HYZMNM3 : rk(Y :: Z :: M :: N :: nil) <= 3).
{
	try assert(HXYZMNeq : rk(X :: Y :: Z :: M :: N :: nil) = 3) by (apply LXYZMN with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (P := P) (Q := Q) ;try assumption).
	assert(HXYZMNMtmp : rk(X :: Y :: Z :: M :: N :: nil) <= 3) by (solve_hyps_max HXYZMNeq HXYZMNM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Y :: Z :: M :: N :: nil) (X :: Y :: Z :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (Y :: Z :: M :: N :: nil) (X :: Y :: Z :: M :: N :: nil) 3 3 HXYZMNMtmp Hcomp Hincl);apply HT.
}

assert(HYZMNM : rk(Y :: Z :: M :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HYZMNm : rk(Y :: Z :: M :: N ::  nil) >= 1) by (solve_hyps_min HYZMNeq HYZMNm1).
intuition.
Qed.
```

### Lines d and h meet
We can then add point R as the intersection of lines YM and ZN (this an instance of Pasch axiom). And the rest is done automatically by our prover.

Statement
```
context
    dimension 3
    layers 1
endofcontext
layer donnees
    points
         Oo A B C Ap Bp Cp X Y Z M N Sp T U V R
    hypotheses
        Oo A : 2
        Oo B : 2
        Oo C : 2
        A B : 2
        A C : 2
        B C : 2
        Oo Ap : 2
        Oo Bp : 2
        Oo Cp : 2
        Ap Bp : 2
        Ap Cp : 2
        Bp Cp : 2
        Oo A B C : 2                # a
        Ap M Sp : 2               # b
        Oo A B C Ap M Sp : 4      # a and b are not coplanar
        Bp N T : 2                # c
        Oo A B C Bp N T : 4       # a and c are not coplanar
        Ap M Sp Bp N T : 4      # b and c are not coplanar
        Cp U V : 2                  # d
        Oo A B C Cp U V : 4         # a and d are not coplanar
        Ap M Sp Cp U V : 4        # b and d are not coplanar
        Bp N T Cp U V : 4         # c and d are not coplanar
        Oo Ap Bp Cp : 2             # e
        Oo A Ap : 3                 # a and e are different
        A M U : 2                 # f
        Oo Ap Bp Cp A M U : 4     # e and f are not coplanar
        B N V : 2                 # g
        Oo Ap Bp Cp B N V : 4     # e and g are not coplanar
        A M U B N V : 4         # f and g are not coplanar
        C Sp T : 2                  # h
        Oo Ap Bp Cp C Sp T : 4      # e and h are not coplanar
        A M U C Sp T : 4          # f and h are not coplanar
        B N V C Sp T : 4          # g and h are not coplanar
        X A Bp : 2                  # 1st Pappus point
        X Ap B : 2
        Y A Cp : 2                  # 2nd Pappus point
        Y Ap C : 2
        Z C Bp : 2                  # 3rd Pappus point
        Z Cp B : 2
        X Y Z : 2                   # Pappus colinearity
        Y M R : 2
        Z N R : 2
    conclusion
        C Sp T Cp U V : 3           # d and h are coplanar
endoflayer 
conclusion
    C Sp T Cp U V : 3
end 
```

Final Lemma 

```
Lemma LCCpSpTUV : 
forall Oo A B C Ap Bp Cp X Y Z M N Sp T U V R ,
rk(Oo :: A ::  nil) = 2 -> 
rk(Oo :: B ::  nil) = 2 -> 
rk(A :: B ::  nil) = 2 ->
rk(Oo :: C ::  nil) = 2 -> 
rk(A :: C ::  nil) = 2 -> 
rk(B :: C ::  nil) = 2 ->
rk(Oo :: A :: B :: C ::  nil) = 2 -> 
rk(Oo :: Ap ::  nil) = 2 -> 
rk(Oo :: A :: Ap ::  nil) = 3 ->
rk(Oo :: Bp ::  nil) = 2 -> 
rk(Ap :: Bp ::  nil) = 2 -> 
rk(Oo :: Cp ::  nil) = 2 ->
rk(Ap :: Cp ::  nil) = 2 -> 
rk(Bp :: Cp ::  nil) = 2 -> 
rk(Oo :: Ap :: Bp :: Cp ::  nil) = 2 ->
rk(B :: Ap :: X ::  nil) = 2 -> 
rk(A :: Bp :: X ::  nil) = 2 -> 
rk(C :: Ap :: Y ::  nil) = 2 ->
rk(A :: Cp :: Y ::  nil) = 2 -> 
rk(C :: Bp :: Z ::  nil) = 2 -> 
rk(B :: Cp :: Z ::  nil) = 2 ->
rk(X :: Y :: Z ::  nil) = 2 -> 
rk(Ap :: M :: Sp ::  nil) = 2 -> 
rk(Oo :: A :: B :: C :: Ap :: M :: Sp ::  nil) = 4 ->
rk(Bp :: N :: T ::  nil) = 2 -> 
rk(Oo :: A :: B :: C :: Bp :: N :: T ::  nil) = 4 -> 
rk(C :: Sp :: T ::  nil) = 2 ->
rk(Oo :: C :: Ap :: Bp :: Cp :: Sp :: T ::  nil) = 4 -> 
rk(Ap :: Bp :: M :: N :: Sp :: T ::  nil) = 4 -> 
rk(A :: M :: U ::  nil) = 2 ->
rk(Oo :: A :: Ap :: Bp :: Cp :: M :: U ::  nil) = 4 -> 
rk(A :: C :: M :: Sp :: T :: U ::  nil) = 4 -> 
rk(B :: N :: V ::  nil) = 2 ->
rk(Oo :: B :: Ap :: Bp :: Cp :: N :: V ::  nil) = 4 -> 
rk(B :: C :: N :: Sp :: T :: V ::  nil) = 4 -> 
rk(Cp :: U :: V ::  nil) = 2 ->
rk(Oo :: A :: B :: C :: Cp :: U :: V ::  nil) = 4 -> 
rk(A :: B :: M :: N :: U :: V ::  nil) = 4 -> 
rk(Ap :: Cp :: M :: Sp :: U :: V ::  nil) = 4 ->
rk(Bp :: Cp :: N :: T :: U :: V ::  nil) = 4 -> 
rk(Y :: M :: R ::  nil) = 2 -> 
rk(Z :: N :: R ::  nil) = 2 
->
rk(C :: Cp :: Sp :: T :: U :: V ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp X Y Z M N Sp T U V R 
HOoAeq HOoBeq HABeq HOoCeq HACeq HBCeq HOoABCeq HOoApeq HOoAApeq HOoBpeq
HApBpeq HOoCpeq HApCpeq HBpCpeq HOoApBpCpeq HBApXeq HABpXeq HCApYeq HACpYeq HCBpZeq
HBCpZeq HXYZeq HApMSpeq HOoABCApMSpeq HBpNTeq HOoABCBpNTeq HCSpTeq HOoCApBpCpSpTeq HApBpMNSpTeq HAMUeq
HOoAApBpCpMUeq HACMSpTUeq HBNVeq HOoBApBpCpNVeq HBCNSpTVeq HCpUVeq HOoABCCpUVeq HABMNUVeq HApCpMSpUVeq HBpCpNTUVeq
HYMReq HZNReq .


assert(HOoACCpSpTUVm2 : rk(Oo :: A :: C :: Cp :: Sp :: T :: U :: V :: nil) >= 2).
{
	try assert(HOoAeq : rk(Oo :: A :: nil) = 2) by (apply LOoA with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (Sp := Sp) (T := T) (U := U) (V := V) (R := R) ;try assumption).
	assert(HOoAmtmp : rk(Oo :: A :: nil) >= 2) by (solve_hyps_min HOoAeq HOoAm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: nil) (Oo :: A :: C :: Cp :: Sp :: T :: U :: V :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: nil) (Oo :: A :: C :: Cp :: Sp :: T :: U :: V :: nil) 2 2 HOoAmtmp Hcomp Hincl);apply HT.
}


assert(HOoACCpSpTUVm3 : rk(Oo :: A :: C :: Cp :: Sp :: T :: U :: V :: nil) >= 3).
{
	try assert(HOoACpeq : rk(Oo :: A :: Cp :: nil) = 3) by (apply LOoACp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (Sp := Sp) (T := T) (U := U) (V := V) (R := R) ;try assumption).
	assert(HOoACpmtmp : rk(Oo :: A :: Cp :: nil) >= 3) by (solve_hyps_min HOoACpeq HOoACpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Cp :: nil) (Oo :: A :: C :: Cp :: Sp :: T :: U :: V :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Cp :: nil) (Oo :: A :: C :: Cp :: Sp :: T :: U :: V :: nil) 3 3 HOoACpmtmp Hcomp Hincl);apply HT.
}


assert(HCCpSpTUVm2 : rk(C :: Cp :: Sp :: T :: U :: V :: nil) >= 2).
{
	try assert(HOoACCpeq : rk(Oo :: A :: C :: Cp :: nil) = 3) by (apply LOoACCp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (Sp := Sp) (T := T) (U := U) (V := V) (R := R) ;try assumption).
	assert(HOoACCpMtmp : rk(Oo :: A :: C :: Cp :: nil) <= 3) by (solve_hyps_max HOoACCpeq HOoACCpM3).
	assert(HOoACCpSpTUVmtmp : rk(Oo :: A :: C :: Cp :: Sp :: T :: U :: V :: nil) >= 3) by (solve_hyps_min HOoACCpSpTUVeq HOoACCpSpTUVm3).
	try assert(HCCpeq : rk(C :: Cp :: nil) = 2) by (apply LCCp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (Sp := Sp) (T := T) (U := U) (V := V) (R := R) ;try assumption).
	assert(HCCpmtmp : rk(C :: Cp :: nil) >= 2) by (solve_hyps_min HCCpeq HCCpm2).
	assert(Hincl : incl (C :: Cp :: nil) (list_inter (Oo :: A :: C :: Cp :: nil) (C :: Cp :: Sp :: T :: U :: V :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Cp :: Sp :: T :: U :: V :: nil) (Oo :: A :: C :: Cp :: C :: Cp :: Sp :: T :: U :: V :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: Cp :: C :: Cp :: Sp :: T :: U :: V :: nil) ((Oo :: A :: C :: Cp :: nil) ++ (C :: Cp :: Sp :: T :: U :: V :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACCpSpTUVmtmp;try rewrite HT2 in HOoACCpSpTUVmtmp.
	assert(HT := rule_4 (Oo :: A :: C :: Cp :: nil) (C :: Cp :: Sp :: T :: U :: V :: nil) (C :: Cp :: nil) 3 2 3 HOoACCpSpTUVmtmp HCCpmtmp HOoACCpMtmp Hincl); apply HT.
}
try clear HOoACCpSpTUVM1. try clear HOoACCpSpTUVM2. try clear HOoACCpSpTUVM3. try clear HOoACCpSpTUVm4. try clear HOoACCpSpTUVm3. try clear HOoACCpSpTUVm2. try clear HOoACCpSpTUVm1. 


assert(HCCpSpTUVm3 : rk(C :: Cp :: Sp :: T :: U :: V :: nil) >= 3).
{
	try assert(HCCpSpeq : rk(C :: Cp :: Sp :: nil) = 3) by (apply LCCpSp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (Sp := Sp) (T := T) (U := U) (V := V) (R := R) ;try assumption).
	assert(HCCpSpmtmp : rk(C :: Cp :: Sp :: nil) >= 3) by (solve_hyps_min HCCpSpeq HCCpSpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (C :: Cp :: Sp :: nil) (C :: Cp :: Sp :: T :: U :: V :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Cp :: Sp :: nil) (C :: Cp :: Sp :: T :: U :: V :: nil) 3 3 HCCpSpmtmp Hcomp Hincl);apply HT.
}


assert(HCCpSpTUVM3 : rk(C :: Cp :: Sp :: T :: U :: V :: nil) <= 3).
{
	try assert(HCCpSpTUVReq : rk(C :: Cp :: Sp :: T :: U :: V :: R :: nil) = 3) by (apply LCCpSpTUVR with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (X := X) (Y := Y) (Z := Z) (M := M) (N := N) (Sp := Sp) (T := T) (U := U) (V := V) (R := R) ;try assumption).
	assert(HCCpSpTUVRMtmp : rk(C :: Cp :: Sp :: T :: U :: V :: R :: nil) <= 3) by (solve_hyps_max HCCpSpTUVReq HCCpSpTUVRM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (C :: Cp :: Sp :: T :: U :: V :: nil) (C :: Cp :: Sp :: T :: U :: V :: R :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (C :: Cp :: Sp :: T :: U :: V :: nil) (C :: Cp :: Sp :: T :: U :: V :: R :: nil) 3 3 HCCpSpTUVRMtmp Hcomp Hincl);apply HT.
}


assert(HCCpSpTUVM : rk(C :: Cp :: Sp :: T :: U :: V ::  nil) <= 4) by (apply rk_upper_dim).
assert(HCCpSpTUVm : rk(C :: Cp :: Sp :: T :: U :: V ::  nil) >= 1) by (solve_hyps_min HCCpSpTUVeq HCCpSpTUVm1).
intuition.
Qed.
```

## Proof of DG implies Pappus

Statement
```
# file dg2papusAlt2.stat
# Proof of DG implies Pappus
context
    dimension 3
    layers 1
endofcontext
layer donnees
    points
        Oo A B C Ap Bp Cp P X Y Z Q A1 B1 Ap1 Bp1 R
    hypotheses
        Oo A B C : 2
        Oo Ap Bp Cp : 2
        Oo A Ap : 3
        Oo B Bp : 3
        Oo C Cp : 3
        A B : 2
        A C : 2
        B C : 2
        Ap Bp : 2
        Ap Cp : 2
        Bp Cp : 2
        Oo A B C Ap Bp Cp P : 4
        A Bp X : 2
        Ap B X : 2
        A Cp Y : 2
        Ap C Y : 2
        B Cp Z : 2
        Bp C Z : 2
        X P Q : 2
        X Q : 2
        P Q : 2
        A P A1 : 2
        A P A1 Cp : 3
        B Q B1 : 2
        Cp A1 B1 : 2
        Ap P Ap1 : 2
        Ap P Ap1 C : 3
        Bp Q Bp1 : 2
        C Ap1 Bp1 : 2
        C Ap1 Bp1 R : 2	# existence and construction of R comes from DG
        Cp A1 B1 R : 2	#
    conclusion
        X Y Z : 2
endoflayer 
conclusion
    X Y Z : 2
end
```

Final Lemma and its proof :
```coq
Lemma LXYZ : 
forall Oo A B C Ap Bp Cp P X Y Z Q A1 B1 Ap1 Bp1 R ,
rk(A :: B ::  nil) = 2 -> 
rk(A :: C ::  nil) = 2 -> 
rk(B :: C ::  nil) = 2 ->
rk(Oo :: A :: B :: C ::  nil) = 2 -> 
rk(Oo :: A :: Ap ::  nil) = 3 -> 
rk(Oo :: B :: Bp ::  nil) = 3 ->
rk(Ap :: Bp ::  nil) = 2 -> 
rk(Oo :: C :: Cp ::  nil) = 3 -> 
rk(Ap :: Cp ::  nil) = 2 ->
rk(Bp :: Cp ::  nil) = 2 -> 
rk(Oo :: Ap :: Bp :: Cp ::  nil) = 2 -> 
rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: P ::  nil) = 4 ->
rk(B :: Ap :: X ::  nil) = 2 -> 
rk(A :: Bp :: X ::  nil) = 2 -> 
rk(C :: Ap :: Y ::  nil) = 2 ->
rk(A :: Cp :: Y ::  nil) = 2 -> 
rk(C :: Bp :: Z ::  nil) = 2 -> 
rk(B :: Cp :: Z ::  nil) = 2 ->
rk(P :: Q ::  nil) = 2 -> 
rk(X :: Q ::  nil) = 2 -> 
rk(P :: X :: Q ::  nil) = 2 ->
rk(A :: P :: A1 ::  nil) = 2 -> 
rk(A :: Cp :: P :: A1 ::  nil) = 3 -> 
rk(B :: Q :: B1 ::  nil) = 2 ->
rk(Cp :: A1 :: B1 ::  nil) = 2 -> 
rk(Ap :: P :: Ap1 ::  nil) = 2 -> 
rk(C :: Ap :: P :: Ap1 ::  nil) = 3 ->
rk(Bp :: Q :: Bp1 ::  nil) = 2 -> 
rk(C :: Ap1 :: Bp1 ::  nil) = 2 -> 
rk(Cp :: A1 :: B1 :: R ::  nil) = 2 ->
rk(C :: Ap1 :: Bp1 :: R ::  nil) = 2 
-> 
rk(X :: Y :: Z ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp P X Y Z Q A1 B1 Ap1 Bp1 R 
HABeq HACeq HBCeq HOoABCeq HOoAApeq HOoBBpeq HApBpeq HOoCCpeq HApCpeq HBpCpeq
HOoApBpCpeq HOoABCApBpCpPeq HBApXeq HABpXeq HCApYeq HACpYeq HCBpZeq HBCpZeq HPQeq HXQeq
HPXQeq HAPA1eq HACpPA1eq HBQB1eq HCpA1B1eq HApPAp1eq HCApPAp1eq HBpQBp1eq HCAp1Bp1eq HCpA1B1Req
HCAp1Bp1Req .


assert(HBCApXYZm2 : rk(B :: C :: Ap :: X :: Y :: Z :: nil) >= 2).
{
	try assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (B :: C :: nil) (B :: C :: Ap :: X :: Y :: Z :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: nil) (B :: C :: Ap :: X :: Y :: Z :: nil) 2 2 HBCmtmp Hcomp Hincl);apply HT.
}


assert(HBCApXYZm3 : rk(B :: C :: Ap :: X :: Y :: Z :: nil) >= 3).
{
	try assert(HBCXeq : rk(B :: C :: X :: nil) = 3) by (apply LBCX with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HBCXmtmp : rk(B :: C :: X :: nil) >= 3) by (solve_hyps_min HBCXeq HBCXm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: X :: nil) (B :: C :: Ap :: X :: Y :: Z :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: X :: nil) (B :: C :: Ap :: X :: Y :: Z :: nil) 3 3 HBCXmtmp Hcomp Hincl);apply HT.
}


assert(HOoACApXYZm2 : rk(Oo :: A :: C :: Ap :: X :: Y :: Z :: nil) >= 2).
{
	try assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: C :: nil) (Oo :: A :: C :: Ap :: X :: Y :: Z :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: nil) (Oo :: A :: C :: Ap :: X :: Y :: Z :: nil) 2 2 HACmtmp Hcomp Hincl);apply HT.
}


assert(HOoACApXYZm3 : rk(Oo :: A :: C :: Ap :: X :: Y :: Z :: nil) >= 3).
{
	try assert(HOoAApeq : rk(Oo :: A :: Ap :: nil) = 3) by (apply LOoAAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 3) by (solve_hyps_min HOoAApeq HOoAApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: X :: Y :: Z :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: X :: Y :: Z :: nil) 3 3 HOoAApmtmp Hcomp Hincl);apply HT.
}


assert(HCApXYZm2 : rk(C :: Ap :: X :: Y :: Z :: nil) >= 2).
{
	try assert(HOoACApeq : rk(Oo :: A :: C :: Ap :: nil) = 3) by (apply LOoACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HOoACApMtmp : rk(Oo :: A :: C :: Ap :: nil) <= 3) by (solve_hyps_max HOoACApeq HOoACApM3).
	assert(HOoACApXYZmtmp : rk(Oo :: A :: C :: Ap :: X :: Y :: Z :: nil) >= 3) by (solve_hyps_min HOoACApXYZeq HOoACApXYZm3).
	try assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hincl : incl (C :: Ap :: nil) (list_inter (Oo :: A :: C :: Ap :: nil) (C :: Ap :: X :: Y :: Z :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: X :: Y :: Z :: nil) (Oo :: A :: C :: Ap :: C :: Ap :: X :: Y :: Z :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: Ap :: C :: Ap :: X :: Y :: Z :: nil) ((Oo :: A :: C :: Ap :: nil) ++ (C :: Ap :: X :: Y :: Z :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACApXYZmtmp;try rewrite HT2 in HOoACApXYZmtmp.
	assert(HT := rule_4 (Oo :: A :: C :: Ap :: nil) (C :: Ap :: X :: Y :: Z :: nil) (C :: Ap :: nil) 3 2 3 HOoACApXYZmtmp HCApmtmp HOoACApMtmp Hincl); apply HT.
}
try clear HOoACApXYZM1. try clear HOoACApXYZM2. try clear HOoACApXYZM3. try clear HOoACApXYZm4. try clear HOoACApXYZm3. try clear HOoACApXYZm2. try clear HOoACApXYZm1. 


assert(HCApXYZm3 : rk(C :: Ap :: X :: Y :: Z :: nil) >= 3).
{
	try assert(HBApXeq : rk(B :: Ap :: X :: nil) = 2) by (apply LBApX with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HBApXMtmp : rk(B :: Ap :: X :: nil) <= 2) by (solve_hyps_max HBApXeq HBApXM2).
	assert(HBCApXYZmtmp : rk(B :: C :: Ap :: X :: Y :: Z :: nil) >= 3) by (solve_hyps_min HBCApXYZeq HBCApXYZm3).
	try assert(HApXeq : rk(Ap :: X :: nil) = 2) by (apply LApX with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HApXmtmp : rk(Ap :: X :: nil) >= 2) by (solve_hyps_min HApXeq HApXm2).
	assert(Hincl : incl (Ap :: X :: nil) (list_inter (B :: Ap :: X :: nil) (C :: Ap :: X :: Y :: Z :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Ap :: X :: Y :: Z :: nil) (B :: Ap :: X :: C :: Ap :: X :: Y :: Z :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: X :: C :: Ap :: X :: Y :: Z :: nil) ((B :: Ap :: X :: nil) ++ (C :: Ap :: X :: Y :: Z :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCApXYZmtmp;try rewrite HT2 in HBCApXYZmtmp.
	assert(HT := rule_4 (B :: Ap :: X :: nil) (C :: Ap :: X :: Y :: Z :: nil) (Ap :: X :: nil) 3 2 2 HBCApXYZmtmp HApXmtmp HBApXMtmp Hincl); apply HT.
}
try clear HBCApXYZM1. try clear HBCApXYZM2. try clear HBCApXYZM3. try clear HBCApXYZm4. try clear HBCApXYZm3. try clear HBCApXYZm2. try clear HBCApXYZm1. 

assert(HXYZm2 : rk(X :: Y :: Z :: nil) >= 2).
{
	try assert(HCApYeq : rk(C :: Ap :: Y :: nil) = 2) by (apply LCApY with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HCApYMtmp : rk(C :: Ap :: Y :: nil) <= 2) by (solve_hyps_max HCApYeq HCApYM2).
	assert(HCApXYZmtmp : rk(C :: Ap :: X :: Y :: Z :: nil) >= 3) by (solve_hyps_min HCApXYZeq HCApXYZm3).
	try assert(HYeq : rk(Y :: nil) = 1) by (apply LY with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HYmtmp : rk(Y :: nil) >= 1) by (solve_hyps_min HYeq HYm1).
	assert(Hincl : incl (Y :: nil) (list_inter (C :: Ap :: Y :: nil) (X :: Y :: Z :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Ap :: X :: Y :: Z :: nil) (C :: Ap :: Y :: X :: Y :: Z :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: Y :: X :: Y :: Z :: nil) ((C :: Ap :: Y :: nil) ++ (X :: Y :: Z :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCApXYZmtmp;try rewrite HT2 in HCApXYZmtmp.
	assert(HT := rule_4 (C :: Ap :: Y :: nil) (X :: Y :: Z :: nil) (Y :: nil) 3 1 2 HCApXYZmtmp HYmtmp HCApYMtmp Hincl); apply HT.
}
try clear HCApXYZM1. try clear HCApXYZM2. try clear HCApXYZM3. try clear HCApXYZm4. try clear HCApXYZm3. try clear HCApXYZm2. try clear HCApXYZm1. 

assert(HXYZM2 : rk(X :: Y :: Z :: nil) <= 2).
{
	try assert(HAXYZeq : rk(A :: X :: Y :: Z :: nil) = 3) by (apply LAXYZ with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HAXYZMtmp : rk(A :: X :: Y :: Z :: nil) <= 3) by (solve_hyps_max HAXYZeq HAXYZM3).
	try assert(HXYZReq : rk(X :: Y :: Z :: R :: nil) = 3) by (apply LXYZR with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HXYZRMtmp : rk(X :: Y :: Z :: R :: nil) <= 3) by (solve_hyps_max HXYZReq HXYZRM3).
	try assert(HAXYZReq : rk(A :: X :: Y :: Z :: R :: nil) = 4) by (apply LAXYZR with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (P := P) (X := X) (Y := Y) (Z := Z) (Q := Q) (A1 := A1) (B1 := B1) (Ap1 := Ap1) (Bp1 := Bp1) (R := R) ;try assumption).
	assert(HAXYZRmtmp : rk(A :: X :: Y :: Z :: R :: nil) >= 4) by (solve_hyps_min HAXYZReq HAXYZRm4).
	assert(Hincl : incl (X :: Y :: Z :: nil) (list_inter (A :: X :: Y :: Z :: nil) (X :: Y :: Z :: R :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: X :: Y :: Z :: R :: nil) (A :: X :: Y :: Z :: X :: Y :: Z :: R :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: X :: Y :: Z :: X :: Y :: Z :: R :: nil) ((A :: X :: Y :: Z :: nil) ++ (X :: Y :: Z :: R :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAXYZRmtmp;try rewrite HT2 in HAXYZRmtmp.
	assert(HT := rule_3 (A :: X :: Y :: Z :: nil) (X :: Y :: Z :: R :: nil) (X :: Y :: Z :: nil) 3 3 4 HAXYZMtmp HXYZRMtmp HAXYZRmtmp Hincl);apply HT.
}


assert(HXYZM : rk(X :: Y :: Z ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HXYZeq HXYZM3).
assert(HXYZm : rk(X :: Y :: Z ::  nil) >= 1) by (solve_hyps_min HXYZeq HXYZm1).
intuition.
Qed.
```
