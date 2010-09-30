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

include "decidable_kit/fintype.ma".

definition setA : ∀T:eqType.T → bool := λT,x.true.

inductive fgraphType (d1 : finType) (d2 : eqType) : Type :=
  | Fgraph : ∀val:list d2. (length ? val) = (count ? (setA d1) (enum d1)) -> fgraphType d1 d2.

definition fval : ∀d1: finType. ∀d2 : eqType. fgraphType d1 d2 → list d2 :=
  λd1,d2,x. match x with [ (Fgraph val _) ⇒ val].
  
definition fproof : ∀d1:finType.∀d2:eqType.∀u. length ? (fval d1 d2 u) = (count ? (setA d1) ?) :=
  λd1:finType.λd2,u. match u return (λx. length ? (fval d1 d2 x) = (count ? (setA d1) (enum d1))) with [
    (Fgraph _ proof) ⇒ proof].

lemma fgraph_eqP : ∀d1:finType.∀d2:eqType.∀f1,f2:fgraphType d1 d2.
  eq_compatible ? f1 f2 (cmp (list_eqType d2) (fval d1 d2 f1) (fval d1 d2 f2)).
intros (d1 d2 f1 f2); cases f1; cases f2; simplify; clear f1 f2;
apply prove_reflect; intros;
 [1: generalize in match H; rewrite > (b2pT ? ? (eqP (list_eqType d2) ? ?) H2); 
     intros; clear H H2; rewrite < (pirrel ? ? ? H1 H3 (eqType_decidable nat_eqType));
     reflexivity
 |2: unfold Not; intros (H3); destruct H3;
     rewrite > (cmp_refl (list_eqType d2)) in H2; destruct H2;]
qed.

definition fgraph_eqType : finType → eqType → eqType ≝ 
  λd1,d2. mk_eqType ? ? (fgraph_eqP d1 d2).

lemma fval_eqE : 
  ∀d1:finType.∀d2:eqType.∀u,v:fgraph_eqType d1 d2. cmp (list_eqType d2) (fval ? ? u) (fval ? ? v) = cmp ? u v.
intros; reflexivity; qed.

(*
lemma fval_inj : injective fval.
Proof. by move => u v; move/eqP; move/fgraph_eqP. Qed.
*)

 (* if the domain is not empty the default is the first elem of the graph *)
lemma fgraph_default : ∀d1:finType.∀d2:eqType. d1 -> fgraph_eqType d1 d2 -> d2.
intros 4 (d1 d2 x f); cases f; fold unfold sort (sort d2);
generalize in match H; clear H; cases val; clear val;
 [2: intros; assumption
 |1: simplify; generalize in match (enum_uniq d1); cases (enum d1);
     unfold setA; simplify; intros (H H1); [1: destruct (H x) | destruct H1]]
qed.

definition infgraph : ∀d1,d2:finType.∀s : list_eqType d2. option (fgraph_eqType d1 d2) :=
  λd1,d2:finType.λs:list d2.
  match eqbP (length ? s) (count ? (setA d1) (enum d1)) 
  with
  [ (reflect_true p) ⇒ Some ? (Fgraph ? ? ? p)
  | (reflect_false p) ⇒ None ?]. 

inductive infgraph_spec (d1, d2 : finType) (s : list_eqType d2) : option (fgraph_eqType d1 d2) -> Type :=
  | Some_tup : ∀u : fgraphType d1 d2. length ? s = (count ? (setA d1) (enum d1)) -> fval ? ? u = s -> infgraph_spec ? ? s (Some ? u)
  | None_tup: notb (eqb (length ? s) (count ? (setA d1) (enum d1))) = true -> infgraph_spec ? ? s (None ?).

lemma infgraphP : ∀d1,d2:finType.∀s:list_eqType d2. infgraph_spec d1 d2 s (infgraph ? ? s).
unfold infgraph; intros; cases (eqbP (length d2 s) (count d1 (setA d1) (enum d1)));
simplify;
 [1: apply (Some_tup d1 d2 s ? H); reflexivity;
 |2: apply None_tup; rewrite > (p2bF ? ? (eqbP ? ?) H). reflexivity]
qed.

definition infgraphseq : 
  ∀d1,d2:finType.list_eqType (list_eqType d2) -> list_eqType (fgraph_eqType d1 d2) :=
  λd1,d2:finType.
    (foldr ? ?
      (λs: list d2.λts:list (fgraphType d1 d2).
         match infgraph d1 d2 s with 
         [ None ⇒ ts
         | (Some u) ⇒ u::ts]) (nil ?)).

lemma count_setA : ∀d:eqType.∀l. count ? (setA d) l = length ? l.
intros; elim l; [reflexivity] simplify; rewrite > H; clear H; reflexivity; qed. 

lemma mem_infgraphseq : 
  ∀d1,d2:finType.∀a:list_eqType (list_eqType d2).∀x:fgraph_eqType d1 d2. 
    mem ? x (infgraphseq d1 d2 a) = mem (list_eqType d2) (fval d1 d2 x) a. 
intros 3 (d1 d2 l); elim l (x hd tl IH x); [1: reflexivity]
simplify; cases (infgraphP d1 d2 hd); simplify;
rewrite > IH; clear IH; [1: rewrite < H1; reflexivity;]
lapply (b2pT ? ? (negbP ?) H) as H1; clear H;
lapply (b2pF ? ? (eqbP ? ?) H1) as H2; clear H1;
cases (mem (list_eqType d2) (fval d1 d2 x) tl); rewrite > orbC; simplify; [reflexivity]
symmetry; apply (p2bF ? ? (eqP ? ? ?)); unfold Not; intros (Exhd);
apply H2; rewrite < Exhd; clear Exhd H2 tl hd l;
generalize in match x; clear x; cases d1 0; simplify; intros; cases s;
simplify; clear s;  rewrite > H1; simplify; reflexivity;
qed.

lemma uniq_infgraphseq : ∀d1,d2,s. uniq ? s = true -> uniq ? (infgraphseq d1 d2 s) = true.
intros 3 (d1 d2 l); elim l (H hd tl IH H); [reflexivity] simplify;
rewrite > (uniq_tail) in H; lapply (b2pT ? ? (andbP ? ?) H); clear H; decompose;
cases (infgraphP d1 d2 hd); simplify;
  [1: rewrite > IH; [2:assumption] rewrite > andbC; simplify;
      rewrite < H3 in H; rewrite > mem_infgraphseq; assumption
  |2: apply IH; assumption]
qed.

definition multes :  
  ∀d:finType.∀e:d.list_eqType (list_eqType d) -> list_eqType (list_eqType d)
 :=
  λd:finType.λe:d.λl:list (list d). map ? ? (λl. e :: l) l.

definition multss : 
  ∀d:finType.∀e:list_eqType d.list_eqType (list_eqType d) -> list_eqType (list_eqType d)
:= 
  λd:finType.λe:list d.λl:list (list d).
    foldr ? ? (λx,acc. (multes ? x l) @ acc) [] e. 

(*
Eval compute in multss (Seq x1 x2) (Seq (Seq x3 x4) (Seq x5 x6)).
-> Seq (Seq x1 x3 x4) (Seq x1 x5 x6) (Seq x2 x3 x4) (Seq x2 x5 x6)
*)

definition iter :=
  λB:eqType.λn:nat.λf:nat→B→B.λacc:B.foldr ? B f acc (iota O n).

(* the sequence of all the strings of length m on the d alphabet *)
definition mkpermr := 
  λd:finType.λm:nat. iter ? m (λx,acc.multss d (enum d) acc) [[]].

lemma mem_multes : 
  ∀d:finType.∀e:d.∀l:list_eqType (list_eqType d).∀s:list_eqType d.
  mem ? s (multes ? e l) = 
  match s in list with [ nil ⇒ false | (cons e1 tl) ⇒ andb (cmp ? e e1) (mem ? tl l)].
intros (d e l s); elim l (hd tl IH); [cases s;simplify;[2: rewrite > andbC] reflexivity]
simplify; rewrite > IH; cases s; simplify; [reflexivity]
unfold list_eqType; simplify;
apply (cmpP ? e s1); cases (lcmp d l1 hd); intros (E); 
[1,2: rewrite > E; simplify; rewrite > cmp_refl; reflexivity
|3,4: rewrite > cmpC; rewrite > E; simplify; reflexivity;]
qed.

lemma mem_concat: 
  ∀d:eqType. ∀x.∀l1,l2:list d.
    mem d x (l1 @ l2) = orb (mem d x l1) (mem d x l2).
intros; elim l1; [reflexivity] simplify; cases (cmp d x a); simplify; [reflexivity|assumption]
qed.

lemma orb_refl : ∀x.orb x x = x. intros (x); cases x; reflexivity; qed. 

lemma mem_multss : 
  ∀d:finType.∀s:list_eqType d.∀l:list_eqType (list_eqType d).∀x:list_eqType d.
  mem ? x (multss ? s l) = 
  match x in list with [ nil ⇒ false | (cons he tl) ⇒ andb (mem ? he s) (mem ? tl l)].
intros (d s l x); elim s; [cases x] simplify; try reflexivity; rewrite > mem_concat;
rewrite > H; clear H; rewrite > mem_multes; cases x; simplify; [reflexivity]
unfold list_eqType; simplify; apply (cmpP ? a s1); intros (E); 
cases (mem d s1 l1);
[1,2: rewrite > E; rewrite > cmp_refl; simplify;
      [rewrite > orb_refl | rewrite > orbC ] reflexivity
|3,4: simplify; rewrite > orbC; simplify; [reflexivity] symmetry;
      apply (p2bF ? ? (andbP ? ?)); unfold Not; intros (H); decompose;
      rewrite > cmpC in H1; rewrite > E in H1; destruct H1;] 
qed.   

lemma mem_mkpermr_size : 
  ∀d:finType.∀m,x. mem (list_eqType d) x (mkpermr d m) = (eqb (length ? x) m).
intros 2 (d m); elim m 0; simplify; [intros (x); cases x; reflexivity]
intros (n IH x); elim x; rewrite > mem_multss; simplify; [reflexivity]
rewrite > mem_finType; simplify; rewrite > IH; reflexivity;
qed.
(*
axiom uniq_concat : ∀d:eqType.∀l1,l2. uniq d (l1@l1) = (andb (uniq ? l1) (andb (uniq ? l2) ())). 

lemma uniq_mkpermr : ∀d:finType.∀m. uniq ? (mkpermr d m) = true.
intros; elim m; [reflexivity] simplify; fold simplify (mkpermr d n);
generalize in match (enum_uniq d); elim (enum d); [reflexivity];
simplify; rewrite 

unfold multss; 
lapply (b2pT ? ? (uniqP (list_eqType d) (mkpermr d n)) H) as H1; clear H;

Proof.
elim=> //= i IHi; elim: enum (uniq_enum d) => //= x e IHe.
move/andP=> [Hx He]; rewrite uniq_cat {}IHe {He}// andbT.
rewrite {1}/multes uniq_maps ?{}IHi; last move=> _ _ [] //.
apply/hasP; case=> s Hs.
by move/mapsP => [s' _ Ds]; rewrite mem_multss -Ds (negbET Hx) in Hs.
Qed.


definition finfgraph_enum := 
  λd1,d2:finType.infgraphseq (mkpermr d2 (count ? (setA d1) (enum d1))).

Lemma maps_tval_fintuple_enum:
  maps (@fval d1 d2) finfgraph_enum = mkpermr d2 (card (setA d1)).
Proof.
rewrite /finfgraph_enum.
have: all (fun s => size s == (card (setA d1))) (mkpermr d2 (card (setA d1))).
  by apply/allP => s; rewrite mem_mkpermr_size.
elim: (mkpermr d2 (card (setA d1))) => //= s s2 IHs; move/andP => [Hs Hs2].
by case: infgraphP => [_ _ /= ->|]; [rewrite (IHs Hs2)|rewrite Hs].
Qed.

  (* good enumeration *)
Lemma finfgraph_enumP : forall u, count (set1 u) finfgraph_enum = 1.
Proof.
move => [s ps].
rewrite /finfgraph_enum count_set1_uniq; last exact (uniq_infgraphseq (uniq_mkpermr d2 (card (setA d1)))).
by rewrite mem_infgraphseq /= mem_mkpermr_size ps set11.
Qed.

Canonical Structure fgraph_finType := FinType finfgraph_enumP.

End FinGraph.

Definition fgraph_of_fun :=
  locked (fun (d1 :finType) (d2 :eqType) (f : d1 -> d2) => Fgraph (size_maps f _)).

Definition fun_of_fgraph :=
  locked
   (fun d1 (d2:eqType) g x =>
      sub (@fgraph_default d1 d2 x g) (fval g) (index x (enum d1))).

Coercion fun_of_fgraph : fgraphType >-> Funclass.
Lemma fgraphP : forall (d1 : finType) (d2 :eqType) (f g : fgraphType d1 d2), f =1 g <-> f = g.
Proof.
move=> d1 d2 f g; split; last by move=>->.
move=> Efg; rewrite -(can_fun_of_fgraph f) -(can_fun_of_fgraph g).
by apply: fval_inj; unlock fgraph_of_fun => /=; apply: eq_maps.
Qed.

CoInductive setType : Type := Sett : fgraphType G bool_finType -> setType.

Definition sval (s : setType) := match s with Sett g => g end.

Lemma can_sval : cancel sval Sett.
Proof. by rewrite /cancel; case => /=. Qed.

Lemma sval_inj : injective sval.
Proof. exact: can_inj can_sval. Qed.

Canonical Structure set_eqType := EqType (can_eq can_sval).

Canonical Structure set_finType := FinType (can_uniq can_sval).

Definition iset_of_fun (f : G -> bool_finType) : setType :=
  locked Sett (fgraph_of_fun f).

*)
