(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

(* This file was automatically generated: do not edit *********************)

include "preamble.ma".

(* From algebra/Basics ****************************************************)

(* NOTATION
Notation Pair := (pair (B:=_)).
*)

(* NOTATION
Notation Proj1 := (proj1 (B:=_)).
*)

(* NOTATION
Notation Proj2 := (proj2 (B:=_)).
*)

(* COERCION
cic:/Coq/ZArith/BinInt/Z_of_nat.con
*)

(* From algebra/CAbGroups *************************************************)

(* COERCION
cic:/CoRN/algebra/CAbGroups/cag_crr.con
*)

(* From algebra/CAbMonoids ************************************************)

(* COERCION
cic:/CoRN/algebra/CAbMonoids/cam_crr.con
*)

(* From algebra/CFields ***************************************************)

(* COERCION
cic:/CoRN/algebra/CFields/cf_crr.con
*)

(* NOTATION
Notation "x [/] y [//] Hy" := (cf_div x y Hy) (at level 80).
*)

(* NOTATION
Notation "{1/} x" := (Frecip x) (at level 2, right associativity).
*)

(* NOTATION
Infix "{/}" := Fdiv (at level 41, no associativity).
*)

(* From algebra/CGroups ***************************************************)

(* COERCION
cic:/CoRN/algebra/CGroups/cg_crr.con
*)

(* NOTATION
Notation "[--] x" := (cg_inv x) (at level 2, right associativity).
*)

(* NOTATION
Infix "[-]" := cg_minus (at level 50, left associativity).
*)

(* NOTATION
Notation "{--} x" := (Finv x) (at level 2, right associativity).
*)

(* NOTATION
Infix "{-}" := Fminus (at level 50, left associativity).
*)

(* From algebra/CLogic ****************************************************)

(* NOTATION
Infix "IFF" := Iff (at level 60, right associativity).
*)

(* NOTATION
Infix "or" := COr (at level 85, right associativity).
*)

(* NOTATION
Infix "and" := CAnd (at level 80, right associativity).
*)

(* NOTATION
Notation "{ x : A  |  P }" := (sigT (fun x : A => P):CProp)
  (at level 0, x at level 99) : type_scope.
*)

(* NOTATION
Notation "{ x : A  |  P  |  Q }" :=
  (sig2T A (fun x : A => P) (fun x : A => Q)) (at level 0, x at level 99) :
  type_scope.
*)

(* NOTATION
Notation ProjT1 := (proj1_sigT _ _).
*)

(* NOTATION
Notation ProjT2 := (proj2_sigT _ _).
*)

(* From algebra/CMonoids **************************************************)

(* COERCION
cic:/CoRN/algebra/CMonoids/cm_crr.con
*)

(* NOTATION
Notation Zero := (cm_unit _).
*)

(* From algebra/COrdAbs ***************************************************)

(* NOTATION
Notation ZeroR := (Zero:R).
*)

(* NOTATION
Notation AbsBig := (absBig _).
*)

(* From algebra/COrdCauchy ************************************************)

(* COERCION
cic:/CoRN/algebra/COrdCauchy/CS_seq.con
*)

(* From algebra/COrdFields ************************************************)

(* COERCION
cic:/CoRN/algebra/COrdFields/cof_crr.con
*)

(* NOTATION
Infix "[<]" := cof_less (at level 70, no associativity).
*)

(* NOTATION
Infix "[>]" := greater (at level 70, no associativity).
*)

(* NOTATION
Infix "[<=]" := leEq (at level 70, no associativity).
*)

(* NOTATION
Notation " x [/]OneNZ" := (x[/] One[//]ring_non_triv _) (at level 20).
*)

(* NOTATION
Notation " x [/]TwoNZ" := (x[/] Two[//]two_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]ThreeNZ" := (x[/] Three[//]three_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]FourNZ" := (x[/] Four[//]four_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]SixNZ" := (x[/] Six[//]six_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]EightNZ" := (x[/] Eight[//]eight_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]NineNZ" := (x[/] Nine[//]nine_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]TwelveNZ" := (x[/] Twelve[//]twelve_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]SixteenNZ" := (x[/] Sixteen[//]sixteen_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]EighteenNZ" := (x[/] Eighteen[//]eighteen_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]TwentyFourNZ" := (x[/] TwentyFour[//]twentyfour_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]FortyEightNZ" := (x[/] FortyEight[//]fortyeight_ap_zero _) (at level 20).
*)

(* From algebra/COrdFields2 ***********************************************)

(* NOTATION
Notation ZeroR := (Zero:R).
*)

(* NOTATION
Notation OneR := (One:R).
*)

(* From algebra/CPoly_ApZero **********************************************)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* From algebra/CPoly_Degree **********************************************)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* NOTATION
Notation FX := (cpoly_cring F).
*)

(* From algebra/CPoly_NthCoeff ********************************************)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* From algebra/CPolynomials **********************************************)

(* NOTATION
Infix "[+X*]" := cpoly_linear_fun' (at level 50, left associativity).
*)

(* NOTATION
Notation RX := (cpoly_cring CR).
*)

(* NOTATION
Infix "!" := cpoly_apply_fun (at level 1, no associativity).
*)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* NOTATION
Notation Cpoly := (cpoly CR).
*)

(* NOTATION
Notation Cpoly_zero := (cpoly_zero CR).
*)

(* NOTATION
Notation Cpoly_linear := (cpoly_linear CR).
*)

(* NOTATION
Notation Cpoly_cring := (cpoly_cring CR).
*)

(* From algebra/CRings ****************************************************)

(* COERCION
cic:/CoRN/algebra/CRings/cr_crr.con
*)

(* NOTATION
Notation One := (cr_one _).
*)

(* NOTATION
Infix "[*]" := cr_mult (at level 40, left associativity).
*)

(* NOTATION
Notation "x [^] n" := (nexp_op _ n x) (at level 20).
*)

(* NOTATION
Notation Two := (nring 2).
*)

(* NOTATION
Notation Three := (nring 3).
*)

(* NOTATION
Notation Four := (nring 4).
*)

(* NOTATION
Notation Six := (nring 6).
*)

(* NOTATION
Notation Eight := (nring 8).
*)

(* NOTATION
Notation Twelve := (nring 12).
*)

(* NOTATION
Notation Sixteen := (nring 16).
*)

(* NOTATION
Notation Nine := (nring 9).
*)

(* NOTATION
Notation Eighteen := (nring 18).
*)

(* NOTATION
Notation TwentyFour := (nring 24).
*)

(* NOTATION
Notation FortyEight := (nring 48).
*)

(* NOTATION
Infix "{*}" := Fmult (at level 40, left associativity).
*)

(* NOTATION
Infix "{**}" := Fscalmult (at level 40, left associativity).
*)

(* NOTATION
Infix "{^}" := Fnth (at level 30, right associativity).
*)

(* From algebra/CSemiGroups ***********************************************)

(* COERCION
cic:/CoRN/algebra/CSemiGroups/csg_crr.con
*)

(* NOTATION
Infix "[+]" := csg_op (at level 50, left associativity).
*)

(* NOTATION
Infix "{+}" := Fplus (at level 50, left associativity).
*)

(* From algebra/CSetoidFun ************************************************)

(* NOTATION
Notation Conj := (conjP _).
*)

(* COERCION
cic:/CoRN/algebra/CSetoidFun/bpfpfun.con
*)

(* NOTATION
Notation BDom := (bpfdom _ _).
*)

(* COERCION
cic:/CoRN/algebra/CSetoidFun/pfpfun.con
*)

(* NOTATION
Notation Dom := (pfdom _).
*)

(* NOTATION
Notation Part := (pfpfun _).
*)

(* NOTATION
Notation "[-C-] x" := (Fconst x) (at level 2, right associativity).
*)

(* NOTATION
Notation FId := (Fid _).
*)

(* NOTATION
Infix "[o]" := Fcomp (at level 65, no associativity).
*)

(* NOTATION
Notation Prj1 := (prj1 _ _ _ _).
*)

(* NOTATION
Notation Prj2 := (prj2 _ _ _ _).
*)

(* From algebra/CSetoids **************************************************)

(* COERCION
cic:/CoRN/algebra/CSetoids/cs_crr.con
*)

(* NOTATION
Infix "[=]" := cs_eq (at level 70, no associativity).
*)

(* NOTATION
Infix "[#]" := cs_ap (at level 70, no associativity).
*)

(* NOTATION
Infix "[~=]" := cs_neq (at level 70, no associativity).
*)

(* COERCION
cic:/CoRN/algebra/CSetoids/csp_pred.con
*)

(* COERCION
cic:/CoRN/algebra/CSetoids/csp'_pred.con
*)

(* COERCION
cic:/CoRN/algebra/CSetoids/csr_rel.con
*)

(* COERCION
cic:/CoRN/algebra/CSetoids/Ccsr_rel.con
*)

(* COERCION
cic:/CoRN/algebra/CSetoids/csf_fun.con
*)

(* COERCION
cic:/CoRN/algebra/CSetoids/csbf_fun.con
*)

(* COERCION
cic:/CoRN/algebra/CSetoids/un_op_fun.con
*)

(* COERCION
cic:/CoRN/algebra/CSetoids/bin_op_bin_fun.con
*)

(* COERCION
cic:/CoRN/algebra/CSetoids/outer_op_bin_fun.con
*)

(* COERCION
cic:/CoRN/algebra/CSetoids/scs_elem.con
*)

(* From algebra/CVectorSpace **********************************************)

(* COERCION
cic:/CoRN/algebra/CVectorSpace/vs_vs.con
*)

(* NOTATION
Infix "[']" := vs_op (at level 30, no associativity).
*)

(* From algebra/Expon *****************************************************)

(* NOTATION
Notation "( x [//] Hx ) [^^] n" := (zexp x Hx n) (at level 0).
*)

(* From complex/CComplex **************************************************)

(* NOTATION
Notation CCX := (cpoly_cring CC).
*)

(* NOTATION
Infix "[+I*]" := cc_set_CC (at level 48, no associativity).
*)

(* From fta/CC_Props ******************************************************)

(* COERCION
cic:/CoRN/fta/CC_Props/CC_seq.con
*)

(* From fta/FTAreg ********************************************************)

(* COERCION
cic:/CoRN/fta/FTAreg/z_el.con
*)

(* COERCION
cic:/CoRN/fta/FTAreg/Kntup.con
*)

(* From ftc/FTC ***********************************************************)

(* NOTATION
Notation "[-S-] F" := (Fprim F) (at level 20).
*)

(* From ftc/Integral ******************************************************)

(* NOTATION
Notation Integral := (integral _ _ Hab).
*)

(* From ftc/MoreIntervals *************************************************)

(* COERCION
cic:/CoRN/ftc/MoreIntervals/iprop.con
*)

(* From ftc/Partitions ****************************************************)

(* COERCION
cic:/CoRN/ftc/Partitions/Pts.con
*)

(* From ftc/RefLemma ******************************************************)

(* NOTATION
Notation g := RL_g.
*)

(* NOTATION
Notation h := RL_h.
*)

(* NOTATION
Notation just1 := (incF _ (Pts_part_lemma _ _ _ _ _ _ HfP _ _)).
*)

(* NOTATION
Notation just2 := (incF _ (Pts_part_lemma _ _ _ _ _ _ HfQ _ _)).
*)

(* NOTATION
Notation just := (fun z => incF _ (Pts_part_lemma _ _ _ _ _ _ z _ _)).
*)

(* From ftc/RefSeparated **************************************************)

(* NOTATION
Notation just1 := (incF _ (Pts_part_lemma _ _ _ _ _ _ gP _ _)).
*)

(* NOTATION
Notation just2 :=
  (incF _ (Pts_part_lemma _ _ _ _ _ _ sep__sep_points_lemma _ _)).
*)

(* From ftc/RefSeparating *************************************************)

(* NOTATION
Notation m := RS'_m.
*)

(* NOTATION
Notation h := RS'_h.
*)

(* NOTATION
Notation just1 := (incF _ (Pts_part_lemma _ _ _ _ _ _ gP _ _)).
*)

(* NOTATION
Notation just2 :=
  (incF _ (Pts_part_lemma _ _ _ _ _ _ sep__part_pts_in_Partition _ _)).
*)

(* From ftc/Rolle *********************************************************)

(* NOTATION
Notation cp := (compact_part a b Hab' d Hd).
*)

(* From ftc/TaylorLemma ***************************************************)

(* NOTATION
Notation A := (Build_subcsetoid_crr IR _ _ TL_compact_a).
*)

(* NOTATION
Notation B := (Build_subcsetoid_crr IR _ _ TL_compact_b).
*)

(* From ftc/WeakIVT *******************************************************)

(* NOTATION
Infix "**" := prodT (at level 20).
*)

(* From metrics/CMetricSpaces *********************************************)

(* COERCION
cic:/CoRN/metrics/CMetricSpaces/scms_crr.con
*)

(* From metrics/CPseudoMSpaces ********************************************)

(* COERCION
cic:/CoRN/metrics/CPseudoMSpaces/cms_crr.con
*)

(* NOTATION
Infix "[-d]" := cms_d (at level 68, left associativity).
*)

(* From model/structures/Nsec *********************************************)

(* NOTATION
Infix "{#N}" := ap_nat (no associativity, at level 90).
*)

(* From model/structures/Qsec *********************************************)

(* NOTATION
Infix "{=Q}" := Qeq (no associativity, at level 90).
*)

(* NOTATION
Infix "{#Q}" := Qap (no associativity, at level 90).
*)

(* NOTATION
Infix "{<Q}" := Qlt (no associativity, at level 90).
*)

(* NOTATION
Infix "{+Q}" := Qplus (no associativity, at level 85).
*)

(* NOTATION
Infix "{*Q}" := Qmult (no associativity, at level 80).
*)

(* NOTATION
Notation "{-Q}" := Qopp (at level 1, left associativity).
*)

(* COERCION
cic:/CoRN/model/structures/Qsec/inject_Z.con
*)

(* From model/structures/Zsec *********************************************)

(* NOTATION
Infix "{#Z}" := ap_Z (no associativity, at level 90).
*)

(* COERCION
cic:/Coq/ZArith/BinInt/Z.ind#xpointer(1/1/2)
*)

(* From reals/Bridges_LUB *************************************************)

(* NOTATION
Notation "( p , q )" := (pairT p q).
*)

(* From reals/CMetricFields ***********************************************)

(* COERCION
cic:/CoRN/reals/CMetricFields/cmf_crr.con
*)

(* NOTATION
Notation MAbs := (cmf_abs _).
*)

(* COERCION
cic:/CoRN/reals/CMetricFields/MCS_seq.con
*)

(* From reals/CReals ******************************************************)

(* COERCION
cic:/CoRN/reals/CReals/crl_crr.con
*)

(* From reals/CauchySeq ***************************************************)

(* NOTATION
Notation PartIR := (PartFunct IR).
*)

(* NOTATION
Notation ProjIR1 := (prj1 IR _ _ _).
*)

(* NOTATION
Notation ProjIR2 := (prj2 IR _ _ _).
*)

(* NOTATION
Notation ZeroR := (Zero:IR).
*)

(* NOTATION
Notation OneR := (One:IR).
*)

(* From reals/Cauchy_CReals ***********************************************)

(* NOTATION
Notation "'R_COrdField''" := (R_COrdField F).
*)

(* From reals/Intervals ***************************************************)

(* NOTATION
Notation Compact := (compact _ _).
*)

(* NOTATION
Notation FRestr := (Frestr (compact_wd _ _ _)).
*)

(* From reals/Q_dense *****************************************************)

(* COERCION
cic:/CoRN/reals/Q_dense/pair_crr.con
*)

(* NOTATION
Notation "( A , B )" := (pairT A B).
*)

(* From reals/Q_in_CReals *************************************************)

(* COERCION
cic:/Coq/NArith/BinPos/nat_of_P.con
*)

(* From reals/R_morphism **************************************************)

(* COERCION
cic:/CoRN/reals/R_morphism/map.con
*)

(* From tactics/FieldReflection *******************************************)

(* NOTATION
Notation II := (interpF F val unop binop pfun).
*)

(* From tactics/GroupReflection *******************************************)

(* NOTATION
Notation II := (interpG G val unop binop pfun).
*)

(* From tactics/RingReflection ********************************************)

(* NOTATION
Notation II := (interpR R val unop binop pfun).
*)

(* From transc/RealPowers *************************************************)

(* NOTATION
Notation "x [!] y [//] Hy" := (power x y Hy) (at level 20).
*)

(* NOTATION
Notation "F {!} G" := (FPower F G) (at level 20).
*)

(* From devel/loeb/per/lst2fun ********************************************)

(* COERCION
cic:/CoRN/devel/loeb/per/lst2fun/F_crr.con
*)

(* COERCION
cic:/CoRN/devel/loeb/per/lst2fun/to_nat.con
*)

