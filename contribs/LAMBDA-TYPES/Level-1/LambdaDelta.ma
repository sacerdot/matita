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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta".

include "Base.ma".

inductive B: Set \def
| Abbr: B
| Abst: B
| Void: B.

inductive F: Set \def
| Appl: F
| Cast: F.

inductive K: Set \def
| Bind: B \to K
| Flat: F \to K.

inductive T: Set \def
| TSort: nat \to T
| TLRef: nat \to T
| THead: K \to (T \to (T \to T)).

inductive TList: Set \def
| TNil: TList
| TCons: T \to (TList \to TList).

definition THeads: K \to (TList \to (T \to T)) \def let rec THeads (k: K) (us: TList): (T \to T) \def (\lambda (t: T).(match us with [TNil \Rightarrow t | (TCons u ul) \Rightarrow (THead k u (THeads k ul t))])) in THeads.

definition s: K \to (nat \to nat) \def \lambda (k: K).(\lambda (i: nat).(match k with [(Bind _) \Rightarrow (S i) | (Flat _) \Rightarrow i])).

axiom not_abbr_abst: not (eq B Abbr Abst) .

axiom not_void_abst: not (eq B Void Abst) .

axiom terms_props__bind_dec: \forall (b1: B).(\forall (b2: B).(or (eq B b1 b2) ((eq B b1 b2) \to (\forall (P: Prop).P)))) .

axiom terms_props__flat_dec: \forall (f1: F).(\forall (f2: F).(or (eq F f1 f2) ((eq F f1 f2) \to (\forall (P: Prop).P)))) .

axiom terms_props__kind_dec: \forall (k1: K).(\forall (k2: K).(or (eq K k1 k2) ((eq K k1 k2) \to (\forall (P: Prop).P)))) .

axiom term_dec: \forall (t1: T).(\forall (t2: T).(or (eq T t1 t2) ((eq T t1 t2) \to (\forall (P: Prop).P)))) .

axiom binder_dec: \forall (t: T).(or (ex_3 B T T (\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(eq T t (THead (Bind b) w u)))))) (\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T t (THead (Bind b) w u)) \to (\forall (P: Prop).P)))))) .

axiom abst_dec: \forall (u: T).(\forall (v: T).(or (ex T (\lambda (t: T).(eq T u (THead (Bind Abst) v t)))) (\forall (t: T).((eq T u (THead (Bind Abst) v t)) \to (\forall (P: Prop).P))))) .

axiom thead_x_y_y: \forall (k: K).(\forall (v: T).(\forall (t: T).((eq T (THead k v t) t) \to (\forall (P: Prop).P)))) .

axiom s_S: \forall (k: K).(\forall (i: nat).(eq nat (s k (S i)) (S (s k i)))) .

axiom s_plus: \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (s k (plus i j)) (plus (s k i) j)))) .

axiom s_plus_sym: \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (s k (plus i j)) (plus i (s k j))))) .

axiom s_minus: \forall (k: K).(\forall (i: nat).(\forall (j: nat).((le j i) \to (eq nat (s k (minus i j)) (minus (s k i) j))))) .

axiom minus_s_s: \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (minus (s k i) (s k j)) (minus i j)))) .

axiom s_le: \forall (k: K).(\forall (i: nat).(\forall (j: nat).((le i j) \to (le (s k i) (s k j))))) .

axiom s_lt: \forall (k: K).(\forall (i: nat).(\forall (j: nat).((lt i j) \to (lt (s k i) (s k j))))) .

axiom s_inj: \forall (k: K).(\forall (i: nat).(\forall (j: nat).((eq nat (s k i) (s k j)) \to (eq nat i j)))) .

axiom s_arith0: \forall (k: K).(\forall (i: nat).(eq nat (minus (s k i) (s k O)) i)) .

axiom s_arith1: \forall (b: B).(\forall (i: nat).(eq nat (minus (s (Bind b) i) (S O)) i)) .

definition wadd: ((nat \to nat)) \to (nat \to (nat \to nat)) \def \lambda (f: ((nat \to nat))).(\lambda (w: nat).(\lambda (n: nat).(match n with [O \Rightarrow w | (S m) \Rightarrow (f m)]))).

definition weight_map: ((nat \to nat)) \to (T \to nat) \def let rec weight_map (f: ((nat \to nat))) (t: T): nat \def (match t with [(TSort _) \Rightarrow O | (TLRef n) \Rightarrow (f n) | (THead k u t0) \Rightarrow (match k with [(Bind b) \Rightarrow (match b with [Abbr \Rightarrow (S (plus (weight_map f u) (weight_map (wadd f (S (weight_map f u))) t0))) | Abst \Rightarrow (S (plus (weight_map f u) (weight_map (wadd f O) t0))) | Void \Rightarrow (S (plus (weight_map f u) (weight_map (wadd f O) t0)))]) | (Flat _) \Rightarrow (S (plus (weight_map f u) (weight_map f t0)))])]) in weight_map.

definition weight: T \to nat \def weight_map (\lambda (_: nat).O).

definition tlt: T \to (T \to Prop) \def \lambda (t1: T).(\lambda (t2: T).(lt (weight t1) (weight t2))).

axiom wadd_le: \forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (\forall (v: nat).(\forall (w: nat).((le v w) \to (\forall (n: nat).(le (wadd f v n) (wadd g w n)))))))) .

axiom wadd_lt: \forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (\forall (v: nat).(\forall (w: nat).((lt v w) \to (\forall (n: nat).(le (wadd f v n) (wadd g w n)))))))) .

axiom wadd_O: \forall (n: nat).(eq nat (wadd (\lambda (_: nat).O) O n) O) .

axiom weight_le: \forall (t: T).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le (weight_map f t) (weight_map g t))))) .

axiom weight_eq: \forall (t: T).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(eq nat (f n) (g n)))) \to (eq nat (weight_map f t) (weight_map g t))))) .

axiom weight_add_O: \forall (t: T).(eq nat (weight_map (wadd (\lambda (_: nat).O) O) t) (weight_map (\lambda (_: nat).O) t)) .

axiom weight_add_S: \forall (t: T).(\forall (m: nat).(le (weight_map (wadd (\lambda (_: nat).O) O) t) (weight_map (wadd (\lambda (_: nat).O) (S m)) t))) .

axiom tlt_trans: \forall (v: T).(\forall (u: T).(\forall (t: T).((tlt u v) \to ((tlt v t) \to (tlt u t))))) .

axiom tlt_head_sx: \forall (k: K).(\forall (u: T).(\forall (t: T).(tlt u (THead k u t)))) .

axiom tlt_head_dx: \forall (k: K).(\forall (u: T).(\forall (t: T).(tlt t (THead k u t)))) .

axiom tlt_wf__q_ind: \forall (P: ((T \to Prop))).(((\forall (n: nat).((\lambda (P: ((T \to Prop))).(\lambda (n0: nat).(\forall (t: T).((eq nat (weight t) n0) \to (P t))))) P n))) \to (\forall (t: T).(P t))) .

axiom tlt_wf_ind: \forall (P: ((T \to Prop))).(((\forall (t: T).(((\forall (v: T).((tlt v t) \to (P v)))) \to (P t)))) \to (\forall (t: T).(P t))) .

inductive iso: T \to (T \to Prop) \def
| iso_sort: \forall (n1: nat).(\forall (n2: nat).(iso (TSort n1) (TSort n2)))
| iso_lref: \forall (i1: nat).(\forall (i2: nat).(iso (TLRef i1) (TLRef i2)))
| iso_head: \forall (k: K).(\forall (v1: T).(\forall (v2: T).(\forall (t1: T).(\forall (t2: T).(iso (THead k v1 t1) (THead k v2 t2)))))).

axiom iso_flats_lref_bind_false: \forall (f: F).(\forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall (t: T).(\forall (vs: TList).((iso (THeads (Flat f) vs (TLRef i)) (THead (Bind b) v t)) \to (\forall (P: Prop).P))))))) .

axiom iso_flats_flat_bind_false: \forall (f1: F).(\forall (f2: F).(\forall (b: B).(\forall (v: T).(\forall (v2: T).(\forall (t: T).(\forall (t2: T).(\forall (vs: TList).((iso (THeads (Flat f1) vs (THead (Flat f2) v2 t2)) (THead (Bind b) v t)) \to (\forall (P: Prop).P))))))))) .

axiom iso_trans: \forall (t1: T).(\forall (t2: T).((iso t1 t2) \to (\forall (t3: T).((iso t2 t3) \to (iso t1 t3))))) .

inductive C: Set \def
| CSort: nat \to C
| CHead: C \to (K \to (T \to C)).

definition r: K \to (nat \to nat) \def \lambda (k: K).(\lambda (i: nat).(match k with [(Bind _) \Rightarrow i | (Flat _) \Rightarrow (S i)])).

definition clen: C \to nat \def let rec clen (c: C): nat \def (match c with [(CSort _) \Rightarrow O | (CHead c0 k _) \Rightarrow (s k (clen c0))]) in clen.

axiom r_S: \forall (k: K).(\forall (i: nat).(eq nat (r k (S i)) (S (r k i)))) .

axiom r_plus: \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (r k (plus i j)) (plus (r k i) j)))) .

axiom r_plus_sym: \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (r k (plus i j)) (plus i (r k j))))) .

axiom r_minus: \forall (i: nat).(\forall (n: nat).((lt n i) \to (\forall (k: K).(eq nat (minus (r k i) (S n)) (r k (minus i (S n))))))) .

axiom r_dis: \forall (k: K).(\forall (P: Prop).(((((\forall (i: nat).(eq nat (r k i) i))) \to P)) \to (((((\forall (i: nat).(eq nat (r k i) (S i)))) \to P)) \to P))) .

axiom s_r: \forall (k: K).(\forall (i: nat).(eq nat (s k (r k i)) (S i))) .

axiom r_arith0: \forall (k: K).(\forall (i: nat).(eq nat (minus (r k (S i)) (S O)) (r k i))) .

axiom r_arith1: \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (minus (r k (S i)) (S j)) (minus (r k i) j)))) .

definition tweight: T \to nat \def let rec tweight (t: T): nat \def (match t with [(TSort _) \Rightarrow (S O) | (TLRef _) \Rightarrow (S O) | (THead _ u t0) \Rightarrow (S (plus (tweight u) (tweight t0)))]) in tweight.

definition cweight: C \to nat \def let rec cweight (c: C): nat \def (match c with [(CSort _) \Rightarrow O | (CHead c0 _ t) \Rightarrow (plus (cweight c0) (tweight t))]) in cweight.

definition clt: C \to (C \to Prop) \def \lambda (c1: C).(\lambda (c2: C).(lt (cweight c1) (cweight c2))).

definition cle: C \to (C \to Prop) \def \lambda (c1: C).(\lambda (c2: C).(le (cweight c1) (cweight c2))).

axiom tweight_lt: \forall (t: T).(lt O (tweight t)) .

axiom clt_cong: \forall (c: C).(\forall (d: C).((clt c d) \to (\forall (k: K).(\forall (t: T).(clt (CHead c k t) (CHead d k t)))))) .

axiom clt_head: \forall (k: K).(\forall (c: C).(\forall (u: T).(clt c (CHead c k u)))) .

axiom clt_wf__q_ind: \forall (P: ((C \to Prop))).(((\forall (n: nat).((\lambda (P: ((C \to Prop))).(\lambda (n0: nat).(\forall (c: C).((eq nat (cweight c) n0) \to (P c))))) P n))) \to (\forall (c: C).(P c))) .

axiom clt_wf_ind: \forall (P: ((C \to Prop))).(((\forall (c: C).(((\forall (d: C).((clt d c) \to (P d)))) \to (P c)))) \to (\forall (c: C).(P c))) .

definition CTail: K \to (T \to (C \to C)) \def let rec CTail (k: K) (t: T) (c: C): C \def (match c with [(CSort n) \Rightarrow (CHead (CSort n) k t) | (CHead d h u) \Rightarrow (CHead (CTail k t d) h u)]) in CTail.

axiom chead_ctail: \forall (c: C).(\forall (t: T).(\forall (k: K).(ex_3 K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead c k t) (CTail h u d)))))))) .

axiom clt_thead: \forall (k: K).(\forall (u: T).(\forall (c: C).(clt c (CTail k u c)))) .

axiom c_tail_ind: \forall (P: ((C \to Prop))).(((\forall (n: nat).(P (CSort n)))) \to (((\forall (c: C).((P c) \to (\forall (k: K).(\forall (t: T).(P (CTail k t c))))))) \to (\forall (c: C).(P c)))) .

definition fweight: C \to (T \to nat) \def \lambda (c: C).(\lambda (t: T).(plus (cweight c) (tweight t))).

definition flt: C \to (T \to (C \to (T \to Prop))) \def \lambda (c1: C).(\lambda (t1: T).(\lambda (c2: C).(\lambda (t2: T).(lt (fweight c1 t1) (fweight c2 t2))))).

axiom flt_thead_sx: \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt c u c (THead k u t))))) .

axiom flt_thead_dx: \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt c t c (THead k u t))))) .

axiom flt_shift: \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt (CHead c k u) t c (THead k u t))))) .

axiom flt_arith0: \forall (k: K).(\forall (c: C).(\forall (t: T).(\forall (i: nat).(flt c t (CHead c k t) (TLRef i))))) .

axiom flt_arith1: \forall (k1: K).(\forall (c1: C).(\forall (c2: C).(\forall (t1: T).((cle (CHead c1 k1 t1) c2) \to (\forall (k2: K).(\forall (t2: T).(\forall (i: nat).(flt c1 t1 (CHead c2 k2 t2) (TLRef i))))))))) .

axiom flt_arith2: \forall (c1: C).(\forall (c2: C).(\forall (t1: T).(\forall (i: nat).((flt c1 t1 c2 (TLRef i)) \to (\forall (k2: K).(\forall (t2: T).(\forall (j: nat).(flt c1 t1 (CHead c2 k2 t2) (TLRef j))))))))) .

axiom flt_wf__q_ind: \forall (P: ((C \to (T \to Prop)))).(((\forall (n: nat).((\lambda (P: ((C \to (T \to Prop)))).(\lambda (n0: nat).(\forall (c: C).(\forall (t: T).((eq nat (fweight c t) n0) \to (P c t)))))) P n))) \to (\forall (c: C).(\forall (t: T).(P c t)))) .

axiom flt_wf_ind: \forall (P: ((C \to (T \to Prop)))).(((\forall (c2: C).(\forall (t2: T).(((\forall (c1: C).(\forall (t1: T).((flt c1 t1 c2 t2) \to (P c1 t1))))) \to (P c2 t2))))) \to (\forall (c: C).(\forall (t: T).(P c t)))) .

definition lref_map: ((nat \to nat)) \to (nat \to (T \to T)) \def let rec lref_map (f: ((nat \to nat))) (d: nat) (t: T): T \def (match t with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u t0) \Rightarrow (THead k (lref_map f d u) (lref_map f (s k d) t0))]) in lref_map.

definition lift: nat \to (nat \to (T \to T)) \def \lambda (h: nat).(\lambda (i: nat).(\lambda (t: T).(lref_map (\lambda (x: nat).(plus x h)) i t))).

definition lifts: nat \to (nat \to (TList \to TList)) \def let rec lifts (h: nat) (d: nat) (ts: TList): TList \def (match ts with [TNil \Rightarrow TNil | (TCons t ts0) \Rightarrow (TCons (lift h d t) (lifts h d ts0))]) in lifts.

axiom lift_sort: \forall (n: nat).(\forall (h: nat).(\forall (d: nat).(eq T (lift h d (TSort n)) (TSort n)))) .

axiom lift_lref_lt: \forall (n: nat).(\forall (h: nat).(\forall (d: nat).((lt n d) \to (eq T (lift h d (TLRef n)) (TLRef n))))) .

axiom lift_lref_ge: \forall (n: nat).(\forall (h: nat).(\forall (d: nat).((le d n) \to (eq T (lift h d (TLRef n)) (TLRef (plus n h)))))) .

axiom lift_head: \forall (k: K).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall (d: nat).(eq T (lift h d (THead k u t)) (THead k (lift h d u) (lift h (s k d) t))))))) .

axiom lift_bind: \forall (b: B).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall (d: nat).(eq T (lift h d (THead (Bind b) u t)) (THead (Bind b) (lift h d u) (lift h (S d) t))))))) .

axiom lift_flat: \forall (f: F).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall (d: nat).(eq T (lift h d (THead (Flat f) u t)) (THead (Flat f) (lift h d u) (lift h d t))))))) .

axiom lift_gen_sort: \forall (h: nat).(\forall (d: nat).(\forall (n: nat).(\forall (t: T).((eq T (TSort n) (lift h d t)) \to (eq T t (TSort n)))))) .

axiom lift_gen_lref: \forall (t: T).(\forall (d: nat).(\forall (h: nat).(\forall (i: nat).((eq T (TLRef i) (lift h d t)) \to (or (land (lt i d) (eq T t (TLRef i))) (land (le (plus d h) i) (eq T t (TLRef (minus i h))))))))) .

axiom lift_gen_lref_lt: \forall (h: nat).(\forall (d: nat).(\forall (n: nat).((lt n d) \to (\forall (t: T).((eq T (TLRef n) (lift h d t)) \to (eq T t (TLRef n))))))) .

axiom lift_gen_lref_false: \forall (h: nat).(\forall (d: nat).(\forall (n: nat).((le d n) \to ((lt n (plus d h)) \to (\forall (t: T).((eq T (TLRef n) (lift h d t)) \to (\forall (P: Prop).P))))))) .

axiom lift_gen_lref_ge: \forall (h: nat).(\forall (d: nat).(\forall (n: nat).((le d n) \to (\forall (t: T).((eq T (TLRef (plus n h)) (lift h d t)) \to (eq T t (TLRef n))))))) .

axiom lift_gen_head: \forall (k: K).(\forall (u: T).(\forall (t: T).(\forall (x: T).(\forall (h: nat).(\forall (d: nat).((eq T (THead k u t) (lift h d x)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T x (THead k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (s k d) z))))))))))) .

axiom lift_gen_bind: \forall (b: B).(\forall (u: T).(\forall (t: T).(\forall (x: T).(\forall (h: nat).(\forall (d: nat).((eq T (THead (Bind b) u t) (lift h d x)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T x (THead (Bind b) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h (S d) z))))))))))) .

axiom lift_gen_flat: \forall (f: F).(\forall (u: T).(\forall (t: T).(\forall (x: T).(\forall (h: nat).(\forall (d: nat).((eq T (THead (Flat f) u t) (lift h d x)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T x (THead (Flat f) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift h d z))))))))))) .

axiom thead_x_lift_y_y: \forall (k: K).(\forall (t: T).(\forall (v: T).(\forall (h: nat).(\forall (d: nat).((eq T (THead k v (lift h d t)) t) \to (\forall (P: Prop).P)))))) .

axiom lift_r: \forall (t: T).(\forall (d: nat).(eq T (lift O d t) t)) .

axiom lift_lref_gt: \forall (d: nat).(\forall (n: nat).((lt d n) \to (eq T (lift (S O) d (TLRef (pred n))) (TLRef n)))) .

axiom lift_inj: \forall (x: T).(\forall (t: T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d x) (lift h d t)) \to (eq T x t))))) .

axiom lift_gen_lift: \forall (t1: T).(\forall (x: T).(\forall (h1: nat).(\forall (h2: nat).(\forall (d1: nat).(\forall (d2: nat).((le d1 d2) \to ((eq T (lift h1 d1 t1) (lift h2 (plus d2 h1) x)) \to (ex2 T (\lambda (t2: T).(eq T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T t1 (lift h2 d2 t2))))))))))) .

axiom lift_free: \forall (t: T).(\forall (h: nat).(\forall (k: nat).(\forall (d: nat).(\forall (e: nat).((le e (plus d h)) \to ((le d e) \to (eq T (lift k e (lift h d t)) (lift (plus k h) d t)))))))) .

axiom lift_d: \forall (t: T).(\forall (h: nat).(\forall (k: nat).(\forall (d: nat).(\forall (e: nat).((le e d) \to (eq T (lift h (plus k d) (lift k e t)) (lift k e (lift h d t)))))))) .

axiom lift_weight_map: \forall (t: T).(\forall (h: nat).(\forall (d: nat).(\forall (f: ((nat \to nat))).(((\forall (m: nat).((le d m) \to (eq nat (f m) O)))) \to (eq nat (weight_map f (lift h d t)) (weight_map f t)))))) .

axiom lift_weight: \forall (t: T).(\forall (h: nat).(\forall (d: nat).(eq nat (weight (lift h d t)) (weight t)))) .

axiom lift_weight_add: \forall (w: nat).(\forall (t: T).(\forall (h: nat).(\forall (d: nat).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).((lt m d) \to (eq nat (g m) (f m))))) \to ((eq nat (g d) w) \to (((\forall (m: nat).((le d m) \to (eq nat (g (S m)) (f m))))) \to (eq nat (weight_map f (lift h d t)) (weight_map g (lift (S h) d t))))))))))) .

axiom lift_weight_add_O: \forall (w: nat).(\forall (t: T).(\forall (h: nat).(\forall (f: ((nat \to nat))).(eq nat (weight_map f (lift h O t)) (weight_map (wadd f w) (lift (S h) O t)))))) .

axiom lift_tlt_dx: \forall (k: K).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall (d: nat).(tlt t (THead k u (lift h d t))))))) .

inductive PList: Set \def
| PNil: PList
| PCons: nat \to (nat \to (PList \to PList)).

definition PConsTail: PList \to (nat \to (nat \to PList)) \def let rec PConsTail (hds: PList): (nat \to (nat \to PList)) \def (\lambda (h0: nat).(\lambda (d0: nat).(match hds with [PNil \Rightarrow (PCons h0 d0 PNil) | (PCons h d hds0) \Rightarrow (PCons h d (PConsTail hds0 h0 d0))]))) in PConsTail.

definition trans: PList \to (nat \to nat) \def let rec trans (hds: PList): (nat \to nat) \def (\lambda (i: nat).(match hds with [PNil \Rightarrow i | (PCons h d hds0) \Rightarrow (let j \def (trans hds0 i) in (match (blt j d) with [true \Rightarrow j | false \Rightarrow (plus j h)]))])) in trans.

definition Ss: PList \to PList \def let rec Ss (hds: PList): PList \def (match hds with [PNil \Rightarrow PNil | (PCons h d hds0) \Rightarrow (PCons h (S d) (Ss hds0))]) in Ss.

definition lift1: PList \to (T \to T) \def let rec lift1 (hds: PList): (T \to T) \def (\lambda (t: T).(match hds with [PNil \Rightarrow t | (PCons h d hds0) \Rightarrow (lift h d (lift1 hds0 t))])) in lift1.

definition lifts1: PList \to (TList \to TList) \def let rec lifts1 (hds: PList) (ts: TList): TList \def (match ts with [TNil \Rightarrow TNil | (TCons t ts0) \Rightarrow (TCons (lift1 hds t) (lifts1 hds ts0))]) in lifts1.

axiom lift1_lref: \forall (hds: PList).(\forall (i: nat).(eq T (lift1 hds (TLRef i)) (TLRef (trans hds i)))) .

axiom lift1_bind: \forall (b: B).(\forall (hds: PList).(\forall (u: T).(\forall (t: T).(eq T (lift1 hds (THead (Bind b) u t)) (THead (Bind b) (lift1 hds u) (lift1 (Ss hds) t)))))) .

axiom lift1_flat: \forall (f: F).(\forall (hds: PList).(\forall (u: T).(\forall (t: T).(eq T (lift1 hds (THead (Flat f) u t)) (THead (Flat f) (lift1 hds u) (lift1 hds t)))))) .

axiom lift1_cons_tail: \forall (t: T).(\forall (h: nat).(\forall (d: nat).(\forall (hds: PList).(eq T (lift1 (PConsTail hds h d) t) (lift1 hds (lift h d t)))))) .

axiom lifts1_flat: \forall (f: F).(\forall (hds: PList).(\forall (t: T).(\forall (ts: TList).(eq T (lift1 hds (THeads (Flat f) ts t)) (THeads (Flat f) (lifts1 hds ts) (lift1 hds t)))))) .

axiom lifts1_nil: \forall (ts: TList).(eq TList (lifts1 PNil ts) ts) .

axiom lifts1_cons: \forall (h: nat).(\forall (d: nat).(\forall (hds: PList).(\forall (ts: TList).(eq TList (lifts1 (PCons h d hds) ts) (lifts h d (lifts1 hds ts)))))) .

axiom lift1_xhg: \forall (hds: PList).(\forall (t: T).(eq T (lift1 (Ss hds) (lift (S O) O t)) (lift (S O) O (lift1 hds t)))) .

axiom lifts1_xhg: \forall (hds: PList).(\forall (ts: TList).(eq TList (lifts1 (Ss hds) (lifts (S O) O ts)) (lifts (S O) O (lifts1 hds ts)))) .

inductive cnt: T \to Prop \def
| cnt_sort: \forall (n: nat).(cnt (TSort n))
| cnt_head: \forall (t: T).((cnt t) \to (\forall (k: K).(\forall (v: T).(cnt (THead k v t))))).

axiom cnt_lift: \forall (t: T).((cnt t) \to (\forall (i: nat).(\forall (d: nat).(cnt (lift i d t))))) .

inductive drop: nat \to (nat \to (C \to (C \to Prop))) \def
| drop_refl: \forall (c: C).(drop O O c c)
| drop_drop: \forall (k: K).(\forall (h: nat).(\forall (c: C).(\forall (e: C).((drop (r k h) O c e) \to (\forall (u: T).(drop (S h) O (CHead c k u) e))))))
| drop_skip: \forall (k: K).(\forall (h: nat).(\forall (d: nat).(\forall (c: C).(\forall (e: C).((drop h (r k d) c e) \to (\forall (u: T).(drop h (S d) (CHead c k (lift h (r k d) u)) (CHead e k u)))))))).

axiom drop_gen_sort: \forall (n: nat).(\forall (h: nat).(\forall (d: nat).(\forall (x: C).((drop h d (CSort n) x) \to (and3 (eq C x (CSort n)) (eq nat h O) (eq nat d O)))))) .

axiom drop_gen_refl: \forall (x: C).(\forall (e: C).((drop O O x e) \to (eq C x e))) .

axiom drop_gen_drop: \forall (k: K).(\forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: nat).((drop (S h) O (CHead c k u) x) \to (drop (r k h) O c x)))))) .

axiom drop_gen_skip_r: \forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: nat).(\forall (d: nat).(\forall (k: K).((drop h (S d) x (CHead c k u)) \to (ex2 C (\lambda (e: C).(eq C x (CHead e k (lift h (r k d) u)))) (\lambda (e: C).(drop h (r k d) e c))))))))) .

axiom drop_gen_skip_l: \forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: nat).(\forall (d: nat).(\forall (k: K).((drop h (S d) (CHead c k u) x) \to (ex3_2 C T (\lambda (e: C).(\lambda (v: T).(eq C x (CHead e k v)))) (\lambda (_: C).(\lambda (v: T).(eq T u (lift h (r k d) v)))) (\lambda (e: C).(\lambda (_: T).(drop h (r k d) c e)))))))))) .

axiom drop_skip_bind: \forall (h: nat).(\forall (d: nat).(\forall (c: C).(\forall (e: C).((drop h d c e) \to (\forall (b: B).(\forall (u: T).(drop h (S d) (CHead c (Bind b) (lift h d u)) (CHead e (Bind b) u)))))))) .

axiom drop_skip_flat: \forall (h: nat).(\forall (d: nat).(\forall (c: C).(\forall (e: C).((drop h (S d) c e) \to (\forall (f: F).(\forall (u: T).(drop h (S d) (CHead c (Flat f) (lift h (S d) u)) (CHead e (Flat f) u)))))))) .

axiom drop_S: \forall (b: B).(\forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (h: nat).((drop h O c (CHead e (Bind b) u)) \to (drop (S h) O c e)))))) .

axiom drop_ctail: \forall (c1: C).(\forall (c2: C).(\forall (d: nat).(\forall (h: nat).((drop h d c1 c2) \to (\forall (k: K).(\forall (u: T).(drop h d (CTail k u c1) (CTail k u c2)))))))) .

axiom drop_mono: \forall (c: C).(\forall (x1: C).(\forall (d: nat).(\forall (h: nat).((drop h d c x1) \to (\forall (x2: C).((drop h d c x2) \to (eq C x1 x2))))))) .

axiom drop_conf_lt: \forall (k: K).(\forall (i: nat).(\forall (u: T).(\forall (c0: C).(\forall (c: C).((drop i O c (CHead c0 k u)) \to (\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h (S (plus i d)) c e) \to (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda (e0: C).(drop i O e (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: C).(drop h (r k d) c0 e0))))))))))))) .

axiom drop_conf_ge: \forall (i: nat).(\forall (a: C).(\forall (c: C).((drop i O c a) \to (\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to ((le (plus d h) i) \to (drop (minus i h) O e a))))))))) .

axiom drop_conf_rev: \forall (j: nat).(\forall (e1: C).(\forall (e2: C).((drop j O e1 e2) \to (\forall (c2: C).(\forall (i: nat).((drop i O c2 e2) \to (ex2 C (\lambda (c1: C).(drop j O c1 c2)) (\lambda (c1: C).(drop i j c1 e1))))))))) .

axiom drop_trans_le: \forall (i: nat).(\forall (d: nat).((le i d) \to (\forall (c1: C).(\forall (c2: C).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: C).((drop i O c2 e2) \to (ex2 C (\lambda (e1: C).(drop i O c1 e1)) (\lambda (e1: C).(drop h (minus d i) e1 e2))))))))))) .

axiom drop_trans_ge: \forall (i: nat).(\forall (c1: C).(\forall (c2: C).(\forall (d: nat).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: C).((drop i O c2 e2) \to ((le d i) \to (drop (plus i h) O c1 e2))))))))) .

inductive drop1: PList \to (C \to (C \to Prop)) \def
| drop1_nil: \forall (c: C).(drop1 PNil c c)
| drop1_cons: \forall (c1: C).(\forall (c2: C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 c2) \to (\forall (c3: C).(\forall (hds: PList).((drop1 hds c2 c3) \to (drop1 (PCons h d hds) c1 c3)))))))).

definition ctrans: PList \to (nat \to (T \to T)) \def let rec ctrans (hds: PList): (nat \to (T \to T)) \def (\lambda (i: nat).(\lambda (t: T).(match hds with [PNil \Rightarrow t | (PCons h d hds0) \Rightarrow (let j \def (trans hds0 i) in (let u \def (ctrans hds0 i t) in (match (blt j d) with [true \Rightarrow (lift h (minus d (S j)) u) | false \Rightarrow u])))]))) in ctrans.

axiom drop1_skip_bind: \forall (b: B).(\forall (e: C).(\forall (hds: PList).(\forall (c: C).(\forall (u: T).((drop1 hds c e) \to (drop1 (Ss hds) (CHead c (Bind b) (lift1 hds u)) (CHead e (Bind b) u))))))) .

axiom drop1_cons_tail: \forall (c2: C).(\forall (c3: C).(\forall (h: nat).(\forall (d: nat).((drop h d c2 c3) \to (\forall (hds: PList).(\forall (c1: C).((drop1 hds c1 c2) \to (drop1 (PConsTail hds h d) c1 c3)))))))) .

axiom lift1_free: \forall (hds: PList).(\forall (i: nat).(\forall (t: T).(eq T (lift1 hds (lift (S i) O t)) (lift (S (trans hds i)) O (ctrans hds i t))))) .

inductive clear: C \to (C \to Prop) \def
| clear_bind: \forall (b: B).(\forall (e: C).(\forall (u: T).(clear (CHead e (Bind b) u) (CHead e (Bind b) u))))
| clear_flat: \forall (e: C).(\forall (c: C).((clear e c) \to (\forall (f: F).(\forall (u: T).(clear (CHead e (Flat f) u) c))))).

inductive getl (h:nat) (c1:C) (c2:C): Prop \def
| getl_intro: \forall (e: C).((drop h O c1 e) \to ((clear e c2) \to (getl h c1 c2))).

definition cimp: C \to (C \to Prop) \def \lambda (c1: C).(\lambda (c2: C).(\forall (b: B).(\forall (d1: C).(\forall (w: T).(\forall (h: nat).((getl h c1 (CHead d1 (Bind b) w)) \to (ex C (\lambda (d2: C).(getl h c2 (CHead d2 (Bind b) w)))))))))).

axiom clear_gen_sort: \forall (x: C).(\forall (n: nat).((clear (CSort n) x) \to (\forall (P: Prop).P))) .

axiom clear_gen_bind: \forall (b: B).(\forall (e: C).(\forall (x: C).(\forall (u: T).((clear (CHead e (Bind b) u) x) \to (eq C x (CHead e (Bind b) u)))))) .

axiom clear_gen_flat: \forall (f: F).(\forall (e: C).(\forall (x: C).(\forall (u: T).((clear (CHead e (Flat f) u) x) \to (clear e x))))) .

axiom clear_gen_flat_r: \forall (f: F).(\forall (x: C).(\forall (e: C).(\forall (u: T).((clear x (CHead e (Flat f) u)) \to (\forall (P: Prop).P))))) .

axiom clear_gen_all: \forall (c1: C).(\forall (c2: C).((clear c1 c2) \to (ex_3 B C T (\lambda (b: B).(\lambda (e: C).(\lambda (u: T).(eq C c2 (CHead e (Bind b) u)))))))) .

axiom drop_clear: \forall (c1: C).(\forall (c2: C).(\forall (i: nat).((drop (S i) O c1 c2) \to (ex2_3 B C T (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(clear c1 (CHead e (Bind b) v))))) (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop i O e c2)))))))) .

axiom drop_clear_O: \forall (b: B).(\forall (c: C).(\forall (e1: C).(\forall (u: T).((clear c (CHead e1 (Bind b) u)) \to (\forall (e2: C).(\forall (i: nat).((drop i O e1 e2) \to (drop (S i) O c e2)))))))) .

axiom drop_clear_S: \forall (x2: C).(\forall (x1: C).(\forall (h: nat).(\forall (d: nat).((drop h (S d) x1 x2) \to (\forall (b: B).(\forall (c2: C).(\forall (u: T).((clear x2 (CHead c2 (Bind b) u)) \to (ex2 C (\lambda (c1: C).(clear x1 (CHead c1 (Bind b) (lift h d u)))) (\lambda (c1: C).(drop h d c1 c2))))))))))) .

axiom clear_clear: \forall (c1: C).(\forall (c2: C).((clear c1 c2) \to (clear c2 c2))) .

axiom clear_mono: \forall (c: C).(\forall (c1: C).((clear c c1) \to (\forall (c2: C).((clear c c2) \to (eq C c1 c2))))) .

axiom clear_trans: \forall (c1: C).(\forall (c: C).((clear c1 c) \to (\forall (c2: C).((clear c c2) \to (clear c1 c2))))) .

axiom clear_ctail: \forall (b: B).(\forall (c1: C).(\forall (c2: C).(\forall (u2: T).((clear c1 (CHead c2 (Bind b) u2)) \to (\forall (k: K).(\forall (u1: T).(clear (CTail k u1 c1) (CHead (CTail k u1 c2) (Bind b) u2)))))))) .

axiom getl_gen_all: \forall (c1: C).(\forall (c2: C).(\forall (i: nat).((getl i c1 c2) \to (ex2 C (\lambda (e: C).(drop i O c1 e)) (\lambda (e: C).(clear e c2)))))) .

axiom getl_gen_sort: \forall (n: nat).(\forall (h: nat).(\forall (x: C).((getl h (CSort n) x) \to (\forall (P: Prop).P)))) .

axiom getl_gen_O: \forall (e: C).(\forall (x: C).((getl O e x) \to (clear e x))) .

axiom getl_gen_S: \forall (k: K).(\forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: nat).((getl (S h) (CHead c k u) x) \to (getl (r k h) c x)))))) .

axiom getl_refl: \forall (b: B).(\forall (c: C).(\forall (u: T).(getl O (CHead c (Bind b) u) (CHead c (Bind b) u)))) .

axiom clear_getl_trans: \forall (i: nat).(\forall (c2: C).(\forall (c3: C).((getl i c2 c3) \to (\forall (c1: C).((clear c1 c2) \to (getl i c1 c3)))))) .

axiom getl_clear_trans: \forall (i: nat).(\forall (c1: C).(\forall (c2: C).((getl i c1 c2) \to (\forall (c3: C).((clear c2 c3) \to (getl i c1 c3)))))) .

axiom getl_head: \forall (k: K).(\forall (h: nat).(\forall (c: C).(\forall (e: C).((getl (r k h) c e) \to (\forall (u: T).(getl (S h) (CHead c k u) e)))))) .

axiom getl_flat: \forall (c: C).(\forall (e: C).(\forall (h: nat).((getl h c e) \to (\forall (f: F).(\forall (u: T).(getl h (CHead c (Flat f) u) e)))))) .

axiom getl_drop: \forall (b: B).(\forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (h: nat).((getl h c (CHead e (Bind b) u)) \to (drop (S h) O c e)))))) .

axiom getl_clear_bind: \forall (b: B).(\forall (c: C).(\forall (e1: C).(\forall (v: T).((clear c (CHead e1 (Bind b) v)) \to (\forall (e2: C).(\forall (n: nat).((getl n e1 e2) \to (getl (S n) c e2)))))))) .

axiom getl_ctail: \forall (b: B).(\forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead d (Bind b) u)) \to (\forall (k: K).(\forall (v: T).(getl i (CTail k v c) (CHead (CTail k v d) (Bind b) u))))))))) .

axiom getl_ctail_clen: \forall (b: B).(\forall (t: T).(\forall (c: C).(ex nat (\lambda (n: nat).(getl (clen c) (CTail (Bind b) t c) (CHead (CSort n) (Bind b) t)))))) .

axiom getl_dec: \forall (c: C).(\forall (i: nat).(or (ex_3 C B T (\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(getl i c (CHead e (Bind b) v)))))) (\forall (d: C).((getl i c d) \to (\forall (P: Prop).P))))) .

axiom clear_cle: \forall (c1: C).(\forall (c2: C).((clear c1 c2) \to (cle c2 c1))) .

axiom getl_flt: \forall (b: B).(\forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead e (Bind b) u)) \to (flt e u c (TLRef i))))))) .

axiom getl_gen_flat: \forall (f: F).(\forall (e: C).(\forall (d: C).(\forall (v: T).(\forall (i: nat).((getl i (CHead e (Flat f) v) d) \to (getl i e d)))))) .

axiom getl_gen_bind: \forall (b: B).(\forall (e: C).(\forall (d: C).(\forall (v: T).(\forall (i: nat).((getl i (CHead e (Bind b) v) d) \to (or (land (eq nat i O) (eq C d (CHead e (Bind b) v))) (ex2 nat (\lambda (j: nat).(eq nat i (S j))) (\lambda (j: nat).(getl j e d))))))))) .

axiom getl_gen_tail: \forall (k: K).(\forall (b: B).(\forall (u1: T).(\forall (u2: T).(\forall (c2: C).(\forall (c1: C).(\forall (i: nat).((getl i (CTail k u1 c1) (CHead c2 (Bind b) u2)) \to (or (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) (\lambda (e: C).(getl i c1 (CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat i (clen c1))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c2 (CSort n)))))))))))) .

axiom cimp_flat_sx: \forall (f: F).(\forall (c: C).(\forall (v: T).(cimp (CHead c (Flat f) v) c))) .

axiom cimp_flat_dx: \forall (f: F).(\forall (c: C).(\forall (v: T).(cimp c (CHead c (Flat f) v)))) .

axiom cimp_bind: \forall (c1: C).(\forall (c2: C).((cimp c1 c2) \to (\forall (b: B).(\forall (v: T).(cimp (CHead c1 (Bind b) v) (CHead c2 (Bind b) v)))))) .

axiom getl_mono: \forall (c: C).(\forall (x1: C).(\forall (h: nat).((getl h c x1) \to (\forall (x2: C).((getl h c x2) \to (eq C x1 x2)))))) .

axiom getl_clear_conf: \forall (i: nat).(\forall (c1: C).(\forall (c3: C).((getl i c1 c3) \to (\forall (c2: C).((clear c1 c2) \to (getl i c2 c3)))))) .

axiom getl_drop_conf_lt: \forall (b: B).(\forall (c: C).(\forall (c0: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead c0 (Bind b) u)) \to (\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h (S (plus i d)) c e) \to (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h d v)))) (\lambda (v: T).(\lambda (e0: C).(getl i e (CHead e0 (Bind b) v)))) (\lambda (_: T).(\lambda (e0: C).(drop h d c0 e0))))))))))))) .

axiom getl_drop_conf_ge: \forall (i: nat).(\forall (a: C).(\forall (c: C).((getl i c a) \to (\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to ((le (plus d h) i) \to (getl (minus i h) e a))))))))) .

axiom getl_conf_ge_drop: \forall (b: B).(\forall (c1: C).(\forall (e: C).(\forall (u: T).(\forall (i: nat).((getl i c1 (CHead e (Bind b) u)) \to (\forall (c2: C).((drop (S O) i c1 c2) \to (drop i O c2 e)))))))) .

axiom getl_conf_le: \forall (i: nat).(\forall (a: C).(\forall (c: C).((getl i c a) \to (\forall (e: C).(\forall (h: nat).((getl h c e) \to ((le h i) \to (getl (minus i h) e a)))))))) .

axiom getl_drop_conf_rev: \forall (j: nat).(\forall (e1: C).(\forall (e2: C).((drop j O e1 e2) \to (\forall (b: B).(\forall (c2: C).(\forall (v2: T).(\forall (i: nat).((getl i c2 (CHead e2 (Bind b) v2)) \to (ex2 C (\lambda (c1: C).(drop j O c1 c2)) (\lambda (c1: C).(drop (S i) j c1 e1))))))))))) .

axiom drop_getl_trans_lt: \forall (i: nat).(\forall (d: nat).((lt i d) \to (\forall (c1: C).(\forall (c2: C).(\forall (h: nat).((drop h d c1 c2) \to (\forall (b: B).(\forall (e2: C).(\forall (v: T).((getl i c2 (CHead e2 (Bind b) v)) \to (ex2 C (\lambda (e1: C).(getl i c1 (CHead e1 (Bind b) (lift h (minus d (S i)) v)))) (\lambda (e1: C).(drop h (minus d (S i)) e1 e2))))))))))))) .

axiom drop_getl_trans_le: \forall (i: nat).(\forall (d: nat).((le i d) \to (\forall (c1: C).(\forall (c2: C).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: C).((getl i c2 e2) \to (ex3_2 C C (\lambda (e0: C).(\lambda (_: C).(drop i O c1 e0))) (\lambda (e0: C).(\lambda (e1: C).(drop h (minus d i) e0 e1))) (\lambda (_: C).(\lambda (e1: C).(clear e1 e2)))))))))))) .

axiom drop_getl_trans_ge: \forall (i: nat).(\forall (c1: C).(\forall (c2: C).(\forall (d: nat).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: C).((getl i c2 e2) \to ((le d i) \to (getl (plus i h) c1 e2))))))))) .

axiom getl_drop_trans: \forall (c1: C).(\forall (c2: C).(\forall (h: nat).((getl h c1 c2) \to (\forall (e2: C).(\forall (i: nat).((drop (S i) O c2 e2) \to (drop (S (plus i h)) O c1 e2))))))) .

axiom getl_trans: \forall (i: nat).(\forall (c1: C).(\forall (c2: C).(\forall (h: nat).((getl h c1 c2) \to (\forall (e2: C).((getl i c2 e2) \to (getl (plus i h) c1 e2))))))) .

axiom drop1_getl_trans: \forall (hds: PList).(\forall (c1: C).(\forall (c2: C).((drop1 hds c2 c1) \to (\forall (b: B).(\forall (e1: C).(\forall (v: T).(\forall (i: nat).((getl i c1 (CHead e1 (Bind b) v)) \to (ex C (\lambda (e2: C).(getl (trans hds i) c2 (CHead e2 (Bind b) (ctrans hds i v))))))))))))) .

axiom cimp_getl_conf: \forall (c1: C).(\forall (c2: C).((cimp c1 c2) \to (\forall (b: B).(\forall (d1: C).(\forall (w: T).(\forall (i: nat).((getl i c1 (CHead d1 (Bind b) w)) \to (ex2 C (\lambda (d2: C).(cimp d1 d2)) (\lambda (d2: C).(getl i c2 (CHead d2 (Bind b) w))))))))))) .

inductive subst0: nat \to (T \to (T \to (T \to Prop))) \def
| subst0_lref: \forall (v: T).(\forall (i: nat).(subst0 i v (TLRef i) (lift (S i) O v)))
| subst0_fst: \forall (v: T).(\forall (u2: T).(\forall (u1: T).(\forall (i: nat).((subst0 i v u1 u2) \to (\forall (t: T).(\forall (k: K).(subst0 i v (THead k u1 t) (THead k u2 t))))))))
| subst0_snd: \forall (k: K).(\forall (v: T).(\forall (t2: T).(\forall (t1: T).(\forall (i: nat).((subst0 (s k i) v t1 t2) \to (\forall (u: T).(subst0 i v (THead k u t1) (THead k u t2))))))))
| subst0_both: \forall (v: T).(\forall (u1: T).(\forall (u2: T).(\forall (i: nat).((subst0 i v u1 u2) \to (\forall (k: K).(\forall (t1: T).(\forall (t2: T).((subst0 (s k i) v t1 t2) \to (subst0 i v (THead k u1 t1) (THead k u2 t2)))))))))).

axiom subst0_gen_sort: \forall (v: T).(\forall (x: T).(\forall (i: nat).(\forall (n: nat).((subst0 i v (TSort n) x) \to (\forall (P: Prop).P))))) .

axiom subst0_gen_lref: \forall (v: T).(\forall (x: T).(\forall (i: nat).(\forall (n: nat).((subst0 i v (TLRef n) x) \to (land (eq nat n i) (eq T x (lift (S n) O v))))))) .

axiom subst0_gen_head: \forall (k: K).(\forall (v: T).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).((subst0 i v (THead k u1 t1) x) \to (or3 (ex2 T (\lambda (u2: T).(eq T x (THead k u2 t1))) (\lambda (u2: T).(subst0 i v u1 u2))) (ex2 T (\lambda (t2: T).(eq T x (THead k u1 t2))) (\lambda (t2: T).(subst0 (s k i) v t1 t2))) (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v u1 u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k i) v t1 t2))))))))))) .

axiom subst0_refl: \forall (u: T).(\forall (t: T).(\forall (d: nat).((subst0 d u t t) \to (\forall (P: Prop).P)))) .

axiom subst0_gen_lift_lt: \forall (u: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).(\forall (h: nat).(\forall (d: nat).((subst0 i (lift h d u) (lift h (S (plus i d)) t1) x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u t1 t2))))))))) .

axiom subst0_gen_lift_false: \forall (t: T).(\forall (u: T).(\forall (x: T).(\forall (h: nat).(\forall (d: nat).(\forall (i: nat).((le d i) \to ((lt i (plus d h)) \to ((subst0 i u (lift h d t) x) \to (\forall (P: Prop).P))))))))) .

axiom subst0_gen_lift_ge: \forall (u: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).(\forall (h: nat).(\forall (d: nat).((subst0 i u (lift h d t1) x) \to ((le (plus d h) i) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(subst0 (minus i h) u t1 t2)))))))))) .

axiom subst0_lift_lt: \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).((subst0 i u t1 t2) \to (\forall (d: nat).((lt i d) \to (\forall (h: nat).(subst0 i (lift h (minus d (S i)) u) (lift h d t1) (lift h d t2))))))))) .

axiom subst0_lift_ge: \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).(\forall (h: nat).((subst0 i u t1 t2) \to (\forall (d: nat).((le d i) \to (subst0 (plus i h) u (lift h d t1) (lift h d t2))))))))) .

axiom subst0_lift_ge_S: \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).((subst0 i u t1 t2) \to (\forall (d: nat).((le d i) \to (subst0 (S i) u (lift (S O) d t1) (lift (S O) d t2)))))))) .

axiom subst0_lift_ge_s: \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).((subst0 i u t1 t2) \to (\forall (d: nat).((le d i) \to (\forall (b: B).(subst0 (s (Bind b) i) u (lift (S O) d t1) (lift (S O) d t2))))))))) .

axiom subst0_subst0: \forall (t1: T).(\forall (t2: T).(\forall (u2: T).(\forall (j: nat).((subst0 j u2 t1 t2) \to (\forall (u1: T).(\forall (u: T).(\forall (i: nat).((subst0 i u u1 u2) \to (ex2 T (\lambda (t: T).(subst0 j u1 t1 t)) (\lambda (t: T).(subst0 (S (plus i j)) u t t2))))))))))) .

axiom subst0_subst0_back: \forall (t1: T).(\forall (t2: T).(\forall (u2: T).(\forall (j: nat).((subst0 j u2 t1 t2) \to (\forall (u1: T).(\forall (u: T).(\forall (i: nat).((subst0 i u u2 u1) \to (ex2 T (\lambda (t: T).(subst0 j u1 t1 t)) (\lambda (t: T).(subst0 (S (plus i j)) u t2 t))))))))))) .

axiom subst0_trans: \forall (t2: T).(\forall (t1: T).(\forall (v: T).(\forall (i: nat).((subst0 i v t1 t2) \to (\forall (t3: T).((subst0 i v t2 t3) \to (subst0 i v t1 t3))))))) .

axiom subst0_confluence_neq: \forall (t0: T).(\forall (t1: T).(\forall (u1: T).(\forall (i1: nat).((subst0 i1 u1 t0 t1) \to (\forall (t2: T).(\forall (u2: T).(\forall (i2: nat).((subst0 i2 u2 t0 t2) \to ((not (eq nat i1 i2)) \to (ex2 T (\lambda (t: T).(subst0 i2 u2 t1 t)) (\lambda (t: T).(subst0 i1 u1 t2 t)))))))))))) .

axiom subst0_confluence_eq: \forall (t0: T).(\forall (t1: T).(\forall (u: T).(\forall (i: nat).((subst0 i u t0 t1) \to (\forall (t2: T).((subst0 i u t0 t2) \to (or4 (eq T t1 t2) (ex2 T (\lambda (t: T).(subst0 i u t1 t)) (\lambda (t: T).(subst0 i u t2 t))) (subst0 i u t1 t2) (subst0 i u t2 t1)))))))) .

axiom subst0_confluence_lift: \forall (t0: T).(\forall (t1: T).(\forall (u: T).(\forall (i: nat).((subst0 i u t0 (lift (S O) i t1)) \to (\forall (t2: T).((subst0 i u t0 (lift (S O) i t2)) \to (eq T t1 t2))))))) .

axiom subst0_weight_le: \forall (u: T).(\forall (t: T).(\forall (z: T).(\forall (d: nat).((subst0 d u t z) \to (\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S d) O u)) (g d)) \to (le (weight_map f z) (weight_map g t)))))))))) .

axiom subst0_weight_lt: \forall (u: T).(\forall (t: T).(\forall (z: T).(\forall (d: nat).((subst0 d u t z) \to (\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S d) O u)) (g d)) \to (lt (weight_map f z) (weight_map g t)))))))))) .

axiom subst0_tlt_head: \forall (u: T).(\forall (t: T).(\forall (z: T).((subst0 O u t z) \to (tlt (THead (Bind Abbr) u z) (THead (Bind Abbr) u t))))) .

axiom subst0_tlt: \forall (u: T).(\forall (t: T).(\forall (z: T).((subst0 O u t z) \to (tlt z (THead (Bind Abbr) u t))))) .

axiom dnf_dec: \forall (w: T).(\forall (t: T).(\forall (d: nat).(ex T (\lambda (v: T).(or (subst0 d w t (lift (S O) d v)) (eq T t (lift (S O) d v))))))) .

inductive subst1 (i:nat) (v:T) (t1:T): T \to Prop \def
| subst1_refl: subst1 i v t1 t1
| subst1_single: \forall (t2: T).((subst0 i v t1 t2) \to (subst1 i v t1 t2)).

axiom subst1_head: \forall (v: T).(\forall (u1: T).(\forall (u2: T).(\forall (i: nat).((subst1 i v u1 u2) \to (\forall (k: K).(\forall (t1: T).(\forall (t2: T).((subst1 (s k i) v t1 t2) \to (subst1 i v (THead k u1 t1) (THead k u2 t2)))))))))) .

axiom subst1_gen_sort: \forall (v: T).(\forall (x: T).(\forall (i: nat).(\forall (n: nat).((subst1 i v (TSort n) x) \to (eq T x (TSort n)))))) .

axiom subst1_gen_lref: \forall (v: T).(\forall (x: T).(\forall (i: nat).(\forall (n: nat).((subst1 i v (TLRef n) x) \to (or (eq T x (TLRef n)) (land (eq nat n i) (eq T x (lift (S n) O v)))))))) .

axiom subst1_gen_head: \forall (k: K).(\forall (v: T).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).((subst1 i v (THead k u1 t1) x) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (t2: T).(subst1 (s k i) v t1 t2)))))))))) .

axiom subst1_gen_lift_lt: \forall (u: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).(\forall (h: nat).(\forall (d: nat).((subst1 i (lift h d u) (lift h (S (plus i d)) t1) x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst1 i u t1 t2))))))))) .

axiom subst1_gen_lift_eq: \forall (t: T).(\forall (u: T).(\forall (x: T).(\forall (h: nat).(\forall (d: nat).(\forall (i: nat).((le d i) \to ((lt i (plus d h)) \to ((subst1 i u (lift h d t) x) \to (eq T x (lift h d t)))))))))) .

axiom subst1_gen_lift_ge: \forall (u: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).(\forall (h: nat).(\forall (d: nat).((subst1 i u (lift h d t1) x) \to ((le (plus d h) i) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(subst1 (minus i h) u t1 t2)))))))))) .

axiom subst1_lift_lt: \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).((subst1 i u t1 t2) \to (\forall (d: nat).((lt i d) \to (\forall (h: nat).(subst1 i (lift h (minus d (S i)) u) (lift h d t1) (lift h d t2))))))))) .

axiom subst1_lift_ge: \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).(\forall (h: nat).((subst1 i u t1 t2) \to (\forall (d: nat).((le d i) \to (subst1 (plus i h) u (lift h d t1) (lift h d t2))))))))) .

axiom subst1_ex: \forall (u: T).(\forall (t1: T).(\forall (d: nat).(ex T (\lambda (t2: T).(subst1 d u t1 (lift (S O) d t2)))))) .

axiom subst1_subst1: \forall (t1: T).(\forall (t2: T).(\forall (u2: T).(\forall (j: nat).((subst1 j u2 t1 t2) \to (\forall (u1: T).(\forall (u: T).(\forall (i: nat).((subst1 i u u1 u2) \to (ex2 T (\lambda (t: T).(subst1 j u1 t1 t)) (\lambda (t: T).(subst1 (S (plus i j)) u t t2))))))))))) .

axiom subst1_subst1_back: \forall (t1: T).(\forall (t2: T).(\forall (u2: T).(\forall (j: nat).((subst1 j u2 t1 t2) \to (\forall (u1: T).(\forall (u: T).(\forall (i: nat).((subst1 i u u2 u1) \to (ex2 T (\lambda (t: T).(subst1 j u1 t1 t)) (\lambda (t: T).(subst1 (S (plus i j)) u t2 t))))))))))) .

axiom subst1_trans: \forall (t2: T).(\forall (t1: T).(\forall (v: T).(\forall (i: nat).((subst1 i v t1 t2) \to (\forall (t3: T).((subst1 i v t2 t3) \to (subst1 i v t1 t3))))))) .

axiom subst1_confluence_neq: \forall (t0: T).(\forall (t1: T).(\forall (u1: T).(\forall (i1: nat).((subst1 i1 u1 t0 t1) \to (\forall (t2: T).(\forall (u2: T).(\forall (i2: nat).((subst1 i2 u2 t0 t2) \to ((not (eq nat i1 i2)) \to (ex2 T (\lambda (t: T).(subst1 i2 u2 t1 t)) (\lambda (t: T).(subst1 i1 u1 t2 t)))))))))))) .

axiom subst1_confluence_eq: \forall (t0: T).(\forall (t1: T).(\forall (u: T).(\forall (i: nat).((subst1 i u t0 t1) \to (\forall (t2: T).((subst1 i u t0 t2) \to (ex2 T (\lambda (t: T).(subst1 i u t1 t)) (\lambda (t: T).(subst1 i u t2 t))))))))) .

axiom subst1_confluence_lift: \forall (t0: T).(\forall (t1: T).(\forall (u: T).(\forall (i: nat).((subst1 i u t0 (lift (S O) i t1)) \to (\forall (t2: T).((subst1 i u t0 (lift (S O) i t2)) \to (eq T t1 t2))))))) .

inductive csubst0: nat \to (T \to (C \to (C \to Prop))) \def
| csubst0_snd: \forall (k: K).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall (u2: T).((subst0 i v u1 u2) \to (\forall (c: C).(csubst0 (s k i) v (CHead c k u1) (CHead c k u2))))))))
| csubst0_fst: \forall (k: K).(\forall (i: nat).(\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (u: T).(csubst0 (s k i) v (CHead c1 k u) (CHead c2 k u))))))))
| csubst0_both: \forall (k: K).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall (u2: T).((subst0 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst0 i v c1 c2) \to (csubst0 (s k i) v (CHead c1 k u1) (CHead c2 k u2)))))))))).

axiom csubst0_snd_bind: \forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall (u2: T).((subst0 i v u1 u2) \to (\forall (c: C).(csubst0 (S i) v (CHead c (Bind b) u1) (CHead c (Bind b) u2)))))))) .

axiom csubst0_fst_bind: \forall (b: B).(\forall (i: nat).(\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (u: T).(csubst0 (S i) v (CHead c1 (Bind b) u) (CHead c2 (Bind b) u)))))))) .

axiom csubst0_both_bind: \forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall (u2: T).((subst0 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst0 i v c1 c2) \to (csubst0 (S i) v (CHead c1 (Bind b) u1) (CHead c2 (Bind b) u2)))))))))) .

axiom csubst0_gen_sort: \forall (x: C).(\forall (v: T).(\forall (i: nat).(\forall (n: nat).((csubst0 i v (CSort n) x) \to (\forall (P: Prop).P))))) .

axiom csubst0_gen_head: \forall (k: K).(\forall (c1: C).(\forall (x: C).(\forall (u1: T).(\forall (v: T).(\forall (i: nat).((csubst0 i v (CHead c1 k u1) x) \to (or3 (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C x (CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v u1 u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (c2: C).(\lambda (_: nat).(eq C x (CHead c2 k u1)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 c2)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c2: C).(\lambda (_: nat).(eq C x (CHead c2 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 u2)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 c2)))))))))))) .

axiom csubst0_drop_gt: \forall (n: nat).(\forall (i: nat).((lt i n) \to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((drop n O c1 e) \to (drop n O c2 e))))))))) .

axiom csubst0_drop_gt_back: \forall (n: nat).(\forall (i: nat).((lt i n) \to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((drop n O c2 e) \to (drop n O c1 e))))))))) .

axiom csubst0_drop_lt: \forall (n: nat).(\forall (i: nat).((lt n i) \to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((drop n O c1 e) \to (or4 (drop n O c2 e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k n)) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k n)) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k n)) v u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (s k n)) v e1 e2)))))))))))))))) .

axiom csubst0_drop_eq: \forall (n: nat).(\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 n v c1 c2) \to (\forall (e: C).((drop n O c1 e) \to (or4 (drop n O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))))))))) .

axiom csubst0_drop_eq_back: \forall (n: nat).(\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 n v c1 c2) \to (\forall (e: C).((drop n O c2 e) \to (or4 (drop n O c1 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop n O c1 (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop n O c1 (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop n O c1 (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))))))))) .

axiom csubst0_clear_O: \forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 O v c1 c2) \to (\forall (c: C).((clear c1 c) \to (clear c2 c)))))) .

axiom csubst0_clear_O_back: \forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 O v c1 c2) \to (\forall (c: C).((clear c2 c) \to (clear c1 c)))))) .

axiom csubst0_clear_S: \forall (c1: C).(\forall (c2: C).(\forall (v: T).(\forall (i: nat).((csubst0 (S i) v c1 c2) \to (\forall (c: C).((clear c1 c) \to (or4 (clear c2 c) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c (CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear c2 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2)))))))))))))) .

axiom csubst0_getl_ge: \forall (i: nat).(\forall (n: nat).((le i n) \to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((getl n c1 e) \to (getl n c2 e))))))))) .

axiom csubst0_getl_lt: \forall (i: nat).(\forall (n: nat).((lt n i) \to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((getl n c1 e) \to (or4 (getl n c2 e) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))))))))))))) .

axiom csubst0_getl_ge_back: \forall (i: nat).(\forall (n: nat).((le i n) \to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((getl n c2 e) \to (getl n c1 e))))))))) .

inductive csubst1 (i:nat) (v:T) (c1:C): C \to Prop \def
| csubst1_refl: csubst1 i v c1 c1
| csubst1_sing: \forall (c2: C).((csubst0 i v c1 c2) \to (csubst1 i v c1 c2)).

axiom csubst1_head: \forall (k: K).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall (u2: T).((subst1 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst1 i v c1 c2) \to (csubst1 (s k i) v (CHead c1 k u1) (CHead c2 k u2)))))))))) .

axiom csubst1_bind: \forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall (u2: T).((subst1 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst1 i v c1 c2) \to (csubst1 (S i) v (CHead c1 (Bind b) u1) (CHead c2 (Bind b) u2)))))))))) .

axiom csubst1_flat: \forall (f: F).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall (u2: T).((subst1 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst1 i v c1 c2) \to (csubst1 i v (CHead c1 (Flat f) u1) (CHead c2 (Flat f) u2)))))))))) .

axiom csubst1_gen_head: \forall (k: K).(\forall (c1: C).(\forall (x: C).(\forall (u1: T).(\forall (v: T).(\forall (i: nat).((csubst1 (s k i) v (CHead c1 k u1) x) \to (ex3_2 T C (\lambda (u2: T).(\lambda (c2: C).(eq C x (CHead c2 k u2)))) (\lambda (u2: T).(\lambda (_: C).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (c2: C).(csubst1 i v c1 c2)))))))))) .

axiom csubst1_getl_ge: \forall (i: nat).(\forall (n: nat).((le i n) \to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst1 i v c1 c2) \to (\forall (e: C).((getl n c1 e) \to (getl n c2 e))))))))) .

axiom csubst1_getl_lt: \forall (i: nat).(\forall (n: nat).((lt n i) \to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst1 i v c1 c2) \to (\forall (e1: C).((getl n c1 e1) \to (ex2 C (\lambda (e2: C).(csubst1 (minus i n) v e1 e2)) (\lambda (e2: C).(getl n c2 e2))))))))))) .

axiom csubst1_getl_ge_back: \forall (i: nat).(\forall (n: nat).((le i n) \to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst1 i v c1 c2) \to (\forall (e: C).((getl n c2 e) \to (getl n c1 e))))))))) .

axiom getl_csubst1: \forall (d: nat).(\forall (c: C).(\forall (e: C).(\forall (u: T).((getl d c (CHead e (Bind Abbr) u)) \to (ex2_2 C C (\lambda (a0: C).(\lambda (_: C).(csubst1 d u c a0))) (\lambda (a0: C).(\lambda (a: C).(drop (S O) d a0 a)))))))) .

inductive fsubst0 (i:nat) (v:T) (c1:C) (t1:T): C \to (T \to Prop) \def
| fsubst0_snd: \forall (t2: T).((subst0 i v t1 t2) \to (fsubst0 i v c1 t1 c1 t2))
| fsubst0_fst: \forall (c2: C).((csubst0 i v c1 c2) \to (fsubst0 i v c1 t1 c2 t1))
| fsubst0_both: \forall (t2: T).((subst0 i v t1 t2) \to (\forall (c2: C).((csubst0 i v c1 c2) \to (fsubst0 i v c1 t1 c2 t2)))).

axiom fsubst0_gen_base: \forall (c1: C).(\forall (c2: C).(\forall (t1: T).(\forall (t2: T).(\forall (v: T).(\forall (i: nat).((fsubst0 i v c1 t1 c2 t2) \to (or3 (land (eq C c1 c2) (subst0 i v t1 t2)) (land (eq T t1 t2) (csubst0 i v c1 c2)) (land (subst0 i v t1 t2) (csubst0 i v c1 c2))))))))) .

record G : Set \def {
 next: (nat \to nat);
 next_lt: (\forall (n: nat).(lt n (next n)))
}.

definition next_plus: G \to (nat \to (nat \to nat)) \def let rec next_plus (g: G) (n: nat) (i: nat): nat \def (match i with [O \Rightarrow n | (S i0) \Rightarrow (next g (next_plus g n i0))]) in next_plus.

axiom next_plus_assoc: \forall (g: G).(\forall (n: nat).(\forall (h1: nat).(\forall (h2: nat).(eq nat (next_plus g (next_plus g n h1) h2) (next_plus g n (plus h1 h2)))))) .

axiom next_plus_next: \forall (g: G).(\forall (n: nat).(\forall (h: nat).(eq nat (next_plus g (next g n) h) (next g (next_plus g n h))))) .

axiom next_plus_lt: \forall (g: G).(\forall (h: nat).(\forall (n: nat).(lt n (next_plus g (next g n) h)))) .

inductive tau0 (g:G): C \to (T \to (T \to Prop)) \def
| tau0_sort: \forall (c: C).(\forall (n: nat).(tau0 g c (TSort n) (TSort (next g n))))
| tau0_abbr: \forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: nat).((getl i c (CHead d (Bind Abbr) v)) \to (\forall (w: T).((tau0 g d v w) \to (tau0 g c (TLRef i) (lift (S i) O w))))))))
| tau0_abst: \forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: nat).((getl i c (CHead d (Bind Abst) v)) \to (\forall (w: T).((tau0 g d v w) \to (tau0 g c (TLRef i) (lift (S i) O v))))))))
| tau0_bind: \forall (b: B).(\forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall (t2: T).((tau0 g (CHead c (Bind b) v) t1 t2) \to (tau0 g c (THead (Bind b) v t1) (THead (Bind b) v t2)))))))
| tau0_appl: \forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall (t2: T).((tau0 g c t1 t2) \to (tau0 g c (THead (Flat Appl) v t1) (THead (Flat Appl) v t2))))))
| tau0_cast: \forall (c: C).(\forall (v1: T).(\forall (v2: T).((tau0 g c v1 v2) \to (\forall (t1: T).(\forall (t2: T).((tau0 g c t1 t2) \to (tau0 g c (THead (Flat Cast) v1 t1) (THead (Flat Cast) v2 t2)))))))).

axiom tau0_lift: \forall (g: G).(\forall (e: C).(\forall (t1: T).(\forall (t2: T).((tau0 g e t1 t2) \to (\forall (c: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to (tau0 g c (lift h d t1) (lift h d t2)))))))))) .

axiom tau0_correct: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t: T).((tau0 g c t1 t) \to (ex T (\lambda (t2: T).(tau0 g c t t2))))))) .

inductive tau1 (g:G) (c:C) (t1:T): T \to Prop \def
| tau1_tau0: \forall (t2: T).((tau0 g c t1 t2) \to (tau1 g c t1 t2))
| tau1_sing: \forall (t: T).((tau1 g c t1 t) \to (\forall (t2: T).((tau0 g c t t2) \to (tau1 g c t1 t2)))).

axiom tau1_trans: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t: T).((tau1 g c t1 t) \to (\forall (t2: T).((tau1 g c t t2) \to (tau1 g c t1 t2))))))) .

axiom tau1_bind: \forall (g: G).(\forall (b: B).(\forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall (t2: T).((tau1 g (CHead c (Bind b) v) t1 t2) \to (tau1 g c (THead (Bind b) v t1) (THead (Bind b) v t2)))))))) .

axiom tau1_appl: \forall (g: G).(\forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall (t2: T).((tau1 g c t1 t2) \to (tau1 g c (THead (Flat Appl) v t1) (THead (Flat Appl) v t2))))))) .

axiom tau1_lift: \forall (g: G).(\forall (e: C).(\forall (t1: T).(\forall (t2: T).((tau1 g e t1 t2) \to (\forall (c: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to (tau1 g c (lift h d t1) (lift h d t2)))))))))) .

axiom tau1_correct: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t: T).((tau1 g c t1 t) \to (ex T (\lambda (t2: T).(tau0 g c t t2))))))) .

axiom tau1_abbr: \forall (g: G).(\forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: nat).((getl i c (CHead d (Bind Abbr) v)) \to (\forall (w: T).((tau1 g d v w) \to (tau1 g c (TLRef i) (lift (S i) O w))))))))) .

axiom tau1_cast2: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).((tau1 g c t1 t2) \to (\forall (v1: T).(\forall (v2: T).((tau0 g c v1 v2) \to (ex2 T (\lambda (v3: T).(tau1 g c v1 v3)) (\lambda (v3: T).(tau1 g c (THead (Flat Cast) v1 t1) (THead (Flat Cast) v3 t2))))))))))) .

axiom tau1_cnt: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t: T).((tau0 g c t1 t) \to (ex2 T (\lambda (t2: T).(tau1 g c t1 t2)) (\lambda (t2: T).(cnt t2))))))) .

inductive A: Set \def
| ASort: nat \to (nat \to A)
| AHead: A \to (A \to A).

definition asucc: G \to (A \to A) \def let rec asucc (g: G) (l: A): A \def (match l with [(ASort n0 n) \Rightarrow (match n0 with [O \Rightarrow (ASort O (next g n)) | (S h) \Rightarrow (ASort h n)]) | (AHead a1 a2) \Rightarrow (AHead a1 (asucc g a2))]) in asucc.

definition aplus: G \to (A \to (nat \to A)) \def let rec aplus (g: G) (a: A) (n: nat): A \def (match n with [O \Rightarrow a | (S n0) \Rightarrow (asucc g (aplus g a n0))]) in aplus.

inductive leq (g:G): A \to (A \to Prop) \def
| leq_sort: \forall (h1: nat).(\forall (h2: nat).(\forall (n1: nat).(\forall (n2: nat).(\forall (k: nat).((eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) k)) \to (leq g (ASort h1 n1) (ASort h2 n2)))))))
| leq_head: \forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall (a3: A).(\forall (a4: A).((leq g a3 a4) \to (leq g (AHead a1 a3) (AHead a2 a4))))))).

axiom leq_gen_sort: \forall (g: G).(\forall (h1: nat).(\forall (n1: nat).(\forall (a2: A).((leq g (ASort h1 n1) a2) \to (ex2_3 nat nat nat (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A a2 (ASort h2 n2))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) k)))))))))) .

axiom leq_gen_head: \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a: A).((leq g (AHead a1 a2) a) \to (ex3_2 A A (\lambda (a3: A).(\lambda (a4: A).(eq A a (AHead a3 a4)))) (\lambda (a3: A).(\lambda (_: A).(leq g a1 a3))) (\lambda (_: A).(\lambda (a4: A).(leq g a2 a4)))))))) .

axiom asucc_gen_sort: \forall (g: G).(\forall (h: nat).(\forall (n: nat).(\forall (a: A).((eq A (ASort h n) (asucc g a)) \to (ex_2 nat nat (\lambda (h0: nat).(\lambda (n0: nat).(eq A a (ASort h0 n0))))))))) .

axiom asucc_gen_head: \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a: A).((eq A (AHead a1 a2) (asucc g a)) \to (ex2 A (\lambda (a0: A).(eq A a (AHead a1 a0))) (\lambda (a0: A).(eq A a2 (asucc g a0)))))))) .

axiom aplus_reg_r: \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (h1: nat).(\forall (h2: nat).((eq A (aplus g a1 h1) (aplus g a2 h2)) \to (\forall (h: nat).(eq A (aplus g a1 (plus h h1)) (aplus g a2 (plus h h2))))))))) .

axiom aplus_assoc: \forall (g: G).(\forall (a: A).(\forall (h1: nat).(\forall (h2: nat).(eq A (aplus g (aplus g a h1) h2) (aplus g a (plus h1 h2)))))) .

axiom aplus_asucc: \forall (g: G).(\forall (h: nat).(\forall (a: A).(eq A (aplus g (asucc g a) h) (asucc g (aplus g a h))))) .

axiom aplus_sort_O_S_simpl: \forall (g: G).(\forall (n: nat).(\forall (k: nat).(eq A (aplus g (ASort O n) (S k)) (aplus g (ASort O (next g n)) k)))) .

axiom aplus_sort_S_S_simpl: \forall (g: G).(\forall (n: nat).(\forall (h: nat).(\forall (k: nat).(eq A (aplus g (ASort (S h) n) (S k)) (aplus g (ASort h n) k))))) .

axiom asucc_repl: \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (leq g (asucc g a1) (asucc g a2))))) .

axiom asucc_inj: \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g (asucc g a1) (asucc g a2)) \to (leq g a1 a2)))) .

axiom aplus_asort_O_simpl: \forall (g: G).(\forall (h: nat).(\forall (n: nat).(eq A (aplus g (ASort O n) h) (ASort O (next_plus g n h))))) .

axiom aplus_asort_le_simpl: \forall (g: G).(\forall (h: nat).(\forall (k: nat).(\forall (n: nat).((le h k) \to (eq A (aplus g (ASort k n) h) (ASort (minus k h) n)))))) .

axiom aplus_asort_simpl: \forall (g: G).(\forall (h: nat).(\forall (k: nat).(\forall (n: nat).(eq A (aplus g (ASort k n) h) (ASort (minus k h) (next_plus g n (minus h k))))))) .

axiom aplus_ahead_simpl: \forall (g: G).(\forall (h: nat).(\forall (a1: A).(\forall (a2: A).(eq A (aplus g (AHead a1 a2) h) (AHead a1 (aplus g a2 h)))))) .

axiom aplus_asucc_false: \forall (g: G).(\forall (a: A).(\forall (h: nat).((eq A (aplus g (asucc g a) h) a) \to (\forall (P: Prop).P)))) .

axiom aplus_inj: \forall (g: G).(\forall (h1: nat).(\forall (h2: nat).(\forall (a: A).((eq A (aplus g a h1) (aplus g a h2)) \to (eq nat h1 h2))))) .

axiom ahead_inj_snd: \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a3: A).(\forall (a4: A).((leq g (AHead a1 a2) (AHead a3 a4)) \to (leq g a2 a4)))))) .

axiom leq_refl: \forall (g: G).(\forall (a: A).(leq g a a)) .

axiom leq_eq: \forall (g: G).(\forall (a1: A).(\forall (a2: A).((eq A a1 a2) \to (leq g a1 a2)))) .

axiom leq_asucc: \forall (g: G).(\forall (a: A).(ex A (\lambda (a0: A).(leq g a (asucc g a0))))) .

axiom leq_sym: \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (leq g a2 a1)))) .

axiom leq_trans: \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall (a3: A).((leq g a2 a3) \to (leq g a1 a3)))))) .

axiom leq_ahead_false: \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g (AHead a1 a2) a1) \to (\forall (P: Prop).P)))) .

axiom leq_ahead_asucc_false: \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g (AHead a1 a2) (asucc g a1)) \to (\forall (P: Prop).P)))) .

axiom leq_asucc_false: \forall (g: G).(\forall (a: A).((leq g (asucc g a) a) \to (\forall (P: Prop).P))) .

definition lweight: A \to nat \def let rec lweight (a: A): nat \def (match a with [(ASort _ _) \Rightarrow O | (AHead a1 a2) \Rightarrow (S (plus (lweight a1) (lweight a2)))]) in lweight.

definition llt: A \to (A \to Prop) \def \lambda (a1: A).(\lambda (a2: A).(lt (lweight a1) (lweight a2))).

axiom lweight_repl: \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (eq nat (lweight a1) (lweight a2))))) .

axiom llt_repl: \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall (a3: A).((llt a1 a3) \to (llt a2 a3)))))) .

axiom llt_trans: \forall (a1: A).(\forall (a2: A).(\forall (a3: A).((llt a1 a2) \to ((llt a2 a3) \to (llt a1 a3))))) .

axiom llt_head_sx: \forall (a1: A).(\forall (a2: A).(llt a1 (AHead a1 a2))) .

axiom llt_head_dx: \forall (a1: A).(\forall (a2: A).(llt a2 (AHead a1 a2))) .

axiom llt_wf__q_ind: \forall (P: ((A \to Prop))).(((\forall (n: nat).((\lambda (P: ((A \to Prop))).(\lambda (n0: nat).(\forall (a: A).((eq nat (lweight a) n0) \to (P a))))) P n))) \to (\forall (a: A).(P a))) .

axiom llt_wf_ind: \forall (P: ((A \to Prop))).(((\forall (a2: A).(((\forall (a1: A).((llt a1 a2) \to (P a1)))) \to (P a2)))) \to (\forall (a: A).(P a))) .

inductive aprem: nat \to (A \to (A \to Prop)) \def
| aprem_zero: \forall (a1: A).(\forall (a2: A).(aprem O (AHead a1 a2) a1))
| aprem_succ: \forall (a2: A).(\forall (a: A).(\forall (i: nat).((aprem i a2 a) \to (\forall (a1: A).(aprem (S i) (AHead a1 a2) a))))).

axiom aprem_repl: \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall (i: nat).(\forall (b2: A).((aprem i a2 b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem i a1 b1))))))))) .

axiom aprem_asucc: \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (i: nat).((aprem i a1 a2) \to (aprem i (asucc g a1) a2))))) .

definition gz: G \def mk_G S lt_n_Sn.

inductive leqz: A \to (A \to Prop) \def
| leqz_sort: \forall (h1: nat).(\forall (h2: nat).(\forall (n1: nat).(\forall (n2: nat).((eq nat (plus h1 n2) (plus h2 n1)) \to (leqz (ASort h1 n1) (ASort h2 n2))))))
| leqz_head: \forall (a1: A).(\forall (a2: A).((leqz a1 a2) \to (\forall (a3: A).(\forall (a4: A).((leqz a3 a4) \to (leqz (AHead a1 a3) (AHead a2 a4))))))).

axiom aplus_gz_le: \forall (k: nat).(\forall (h: nat).(\forall (n: nat).((le h k) \to (eq A (aplus gz (ASort h n) k) (ASort O (plus (minus k h) n)))))) .

axiom aplus_gz_ge: \forall (n: nat).(\forall (k: nat).(\forall (h: nat).((le k h) \to (eq A (aplus gz (ASort h n) k) (ASort (minus h k) n))))) .

axiom next_plus_gz: \forall (n: nat).(\forall (h: nat).(eq nat (next_plus gz n h) (plus h n))) .

axiom leqz_leq: \forall (a1: A).(\forall (a2: A).((leq gz a1 a2) \to (leqz a1 a2))) .

axiom leq_leqz: \forall (a1: A).(\forall (a2: A).((leqz a1 a2) \to (leq gz a1 a2))) .

inductive arity (g:G): C \to (T \to (A \to Prop)) \def
| arity_sort: \forall (c: C).(\forall (n: nat).(arity g c (TSort n) (ASort O n)))
| arity_abbr: \forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead d (Bind Abbr) u)) \to (\forall (a: A).((arity g d u a) \to (arity g c (TLRef i) a)))))))
| arity_abst: \forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead d (Bind Abst) u)) \to (\forall (a: A).((arity g d u (asucc g a)) \to (arity g c (TLRef i) a)))))))
| arity_bind: \forall (b: B).((not (eq B b Abst)) \to (\forall (c: C).(\forall (u: T).(\forall (a1: A).((arity g c u a1) \to (\forall (t: T).(\forall (a2: A).((arity g (CHead c (Bind b) u) t a2) \to (arity g c (THead (Bind b) u t) a2)))))))))
| arity_head: \forall (c: C).(\forall (u: T).(\forall (a1: A).((arity g c u (asucc g a1)) \to (\forall (t: T).(\forall (a2: A).((arity g (CHead c (Bind Abst) u) t a2) \to (arity g c (THead (Bind Abst) u t) (AHead a1 a2))))))))
| arity_appl: \forall (c: C).(\forall (u: T).(\forall (a1: A).((arity g c u a1) \to (\forall (t: T).(\forall (a2: A).((arity g c t (AHead a1 a2)) \to (arity g c (THead (Flat Appl) u t) a2)))))))
| arity_cast: \forall (c: C).(\forall (u: T).(\forall (a: A).((arity g c u (asucc g a)) \to (\forall (t: T).((arity g c t a) \to (arity g c (THead (Flat Cast) u t) a))))))
| arity_repl: \forall (c: C).(\forall (t: T).(\forall (a1: A).((arity g c t a1) \to (\forall (a2: A).((leq g a1 a2) \to (arity g c t a2)))))).

axiom arity_gen_sort: \forall (g: G).(\forall (c: C).(\forall (n: nat).(\forall (a: A).((arity g c (TSort n) a) \to (leq g a (ASort O n)))))) .

axiom arity_gen_lref: \forall (g: G).(\forall (c: C).(\forall (i: nat).(\forall (a: A).((arity g c (TLRef i) a) \to (or (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i c (CHead d (Bind Abbr) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u a)))) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i c (CHead d (Bind Abst) u)))) (\lambda (d: C).(\lambda (u: T).(arity g d u (asucc g a)))))))))) .

axiom arity_gen_bind: \forall (b: B).((not (eq B b Abst)) \to (\forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t: T).(\forall (a2: A).((arity g c (THead (Bind b) u t) a2) \to (ex2 A (\lambda (a1: A).(arity g c u a1)) (\lambda (_: A).(arity g (CHead c (Bind b) u) t a2)))))))))) .

axiom arity_gen_abst: \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t: T).(\forall (a: A).((arity g c (THead (Bind Abst) u t) a) \to (ex3_2 A A (\lambda (a1: A).(\lambda (a2: A).(eq A a (AHead a1 a2)))) (\lambda (a1: A).(\lambda (_: A).(arity g c u (asucc g a1)))) (\lambda (_: A).(\lambda (a2: A).(arity g (CHead c (Bind Abst) u) t a2))))))))) .

axiom arity_gen_appl: \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t: T).(\forall (a2: A).((arity g c (THead (Flat Appl) u t) a2) \to (ex2 A (\lambda (a1: A).(arity g c u a1)) (\lambda (a1: A).(arity g c t (AHead a1 a2))))))))) .

axiom arity_gen_cast: \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t: T).(\forall (a: A).((arity g c (THead (Flat Cast) u t) a) \to (land (arity g c u (asucc g a)) (arity g c t a))))))) .

axiom arity_gen_appls: \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (vs: TList).(\forall (a2: A).((arity g c (THeads (Flat Appl) vs t) a2) \to (ex A (\lambda (a: A).(arity g c t a)))))))) .

axiom node_inh: \forall (g: G).(\forall (n: nat).(\forall (k: nat).(ex_2 C T (\lambda (c: C).(\lambda (t: T).(arity g c t (ASort k n))))))) .

axiom arity_gen_cvoid_subst0: \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t a) \to (\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead d (Bind Void) u)) \to (\forall (w: T).(\forall (v: T).((subst0 i w t v) \to (\forall (P: Prop).P)))))))))))) .

axiom arity_gen_cvoid: \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t a) \to (\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead d (Bind Void) u)) \to (ex T (\lambda (v: T).(eq T t (lift (S O) i v)))))))))))) .

axiom arity_gen_lift: \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).(\forall (h: nat).(\forall (d: nat).((arity g c1 (lift h d t) a) \to (\forall (c2: C).((drop h d c1 c2) \to (arity g c2 t a))))))))) .

axiom arity_lift: \forall (g: G).(\forall (c2: C).(\forall (t: T).(\forall (a: A).((arity g c2 t a) \to (\forall (c1: C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 c2) \to (arity g c1 (lift h d t) a))))))))) .

axiom arity_lift1: \forall (g: G).(\forall (a: A).(\forall (c2: C).(\forall (hds: PList).(\forall (c1: C).(\forall (t: T).((drop1 hds c1 c2) \to ((arity g c2 t a) \to (arity g c1 (lift1 hds t) a)))))))) .

axiom arity_mono: \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a1: A).((arity g c t a1) \to (\forall (a2: A).((arity g c t a2) \to (leq g a1 a2))))))) .

axiom arity_cimp_conf: \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).((arity g c1 t a) \to (\forall (c2: C).((cimp c1 c2) \to (arity g c2 t a))))))) .

axiom arity_aprem: \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t a) \to (\forall (i: nat).(\forall (b: A).((aprem i a b) \to (ex2_3 C T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d c)))) (\lambda (d: C).(\lambda (u: T).(\lambda (_: nat).(arity g d u (asucc g b))))))))))))) .

axiom arity_appls_cast: \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t: T).(\forall (vs: TList).(\forall (a: A).((arity g c (THeads (Flat Appl) vs u) (asucc g a)) \to ((arity g c (THeads (Flat Appl) vs t) a) \to (arity g c (THeads (Flat Appl) vs (THead (Flat Cast) u t)) a)))))))) .

axiom arity_appls_abbr: \forall (g: G).(\forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: nat).((getl i c (CHead d (Bind Abbr) v)) \to (\forall (vs: TList).(\forall (a: A).((arity g c (THeads (Flat Appl) vs (lift (S i) O v)) a) \to (arity g c (THeads (Flat Appl) vs (TLRef i)) a))))))))) .

axiom arity_appls_bind: \forall (g: G).(\forall (b: B).((not (eq B b Abst)) \to (\forall (c: C).(\forall (v: T).(\forall (a1: A).((arity g c v a1) \to (\forall (t: T).(\forall (vs: TList).(\forall (a2: A).((arity g (CHead c (Bind b) v) (THeads (Flat Appl) (lifts (S O) O vs) t) a2) \to (arity g c (THeads (Flat Appl) vs (THead (Bind b) v t)) a2))))))))))) .

axiom arity_fsubst0: \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (a: A).((arity g c1 t1 a) \to (\forall (d1: C).(\forall (u: T).(\forall (i: nat).((getl i c1 (CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).(\forall (t2: T).((fsubst0 i u c1 t1 c2 t2) \to (arity g c2 t2 a)))))))))))) .

axiom arity_subst0: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (a: A).((arity g c t1 a) \to (\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead d (Bind Abbr) u)) \to (\forall (t2: T).((subst0 i u t1 t2) \to (arity g c t2 a))))))))))) .

inductive pr0: T \to (T \to Prop) \def
| pr0_refl: \forall (t: T).(pr0 t t)
| pr0_comp: \forall (u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (k: K).(pr0 (THead k u1 t1) (THead k u2 t2))))))))
| pr0_beta: \forall (u: T).(\forall (v1: T).(\forall (v2: T).((pr0 v1 v2) \to (\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (pr0 (THead (Flat Appl) v1 (THead (Bind Abst) u t1)) (THead (Bind Abbr) v2 t2))))))))
| pr0_upsilon: \forall (b: B).((not (eq B b Abst)) \to (\forall (v1: T).(\forall (v2: T).((pr0 v1 v2) \to (\forall (u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (pr0 (THead (Flat Appl) v1 (THead (Bind b) u1 t1)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2)))))))))))))
| pr0_delta: \forall (u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (w: T).((subst0 O u2 t2 w) \to (pr0 (THead (Bind Abbr) u1 t1) (THead (Bind Abbr) u2 w)))))))))
| pr0_zeta: \forall (b: B).((not (eq B b Abst)) \to (\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (u: T).(pr0 (THead (Bind b) u (lift (S O) O t1)) t2))))))
| pr0_epsilon: \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (u: T).(pr0 (THead (Flat Cast) u t1) t2)))).

axiom pr0_gen_sort: \forall (x: T).(\forall (n: nat).((pr0 (TSort n) x) \to (eq T x (TSort n)))) .

axiom pr0_gen_lref: \forall (x: T).(\forall (n: nat).((pr0 (TLRef n) x) \to (eq T x (TLRef n)))) .

axiom pr0_gen_abst: \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Abst) u1 t1) x) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2))))))) .

axiom pr0_gen_appl: \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Flat Appl) u1 t1) x) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t2: T).(eq T x (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O u2) t2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))))))))) .

axiom pr0_gen_cast: \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Flat Cast) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 x))))) .

axiom pr0_lift: \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (h: nat).(\forall (d: nat).(pr0 (lift h d t1) (lift h d t2)))))) .

axiom pr0_gen_abbr: \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Abbr) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u2 y t2))))))) (pr0 t1 (lift (S O) O x)))))) .

axiom pr0_gen_void: \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Void) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O x)))))) .

axiom pr0_gen_lift: \forall (t1: T).(\forall (x: T).(\forall (h: nat).(\forall (d: nat).((pr0 (lift h d t1) x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(pr0 t1 t2))))))) .

axiom pr0_subst0_back: \forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall (i: nat).((subst0 i u2 t1 t2) \to (\forall (u1: T).((pr0 u1 u2) \to (ex2 T (\lambda (t: T).(subst0 i u1 t1 t)) (\lambda (t: T).(pr0 t t2))))))))) .

axiom pr0_subst0_fwd: \forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall (i: nat).((subst0 i u2 t1 t2) \to (\forall (u1: T).((pr0 u2 u1) \to (ex2 T (\lambda (t: T).(subst0 i u1 t1 t)) (\lambda (t: T).(pr0 t2 t))))))))) .

axiom pr0_subst0: \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (v1: T).(\forall (w1: T).(\forall (i: nat).((subst0 i v1 t1 w1) \to (\forall (v2: T).((pr0 v1 v2) \to (or (pr0 w1 t2) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v2 t2 w2)))))))))))) .

axiom pr0_confluence__pr0_cong_upsilon_refl: \forall (b: B).((not (eq B b Abst)) \to (\forall (u0: T).(\forall (u3: T).((pr0 u0 u3) \to (\forall (t4: T).(\forall (t5: T).((pr0 t4 t5) \to (\forall (u2: T).(\forall (v2: T).(\forall (x: T).((pr0 u2 x) \to ((pr0 v2 x) \to (ex2 T (\lambda (t: T).(pr0 (THead (Flat Appl) u2 (THead (Bind b) u0 t4)) t)) (\lambda (t: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t5)) t))))))))))))))) .

axiom pr0_confluence__pr0_cong_upsilon_cong: \forall (b: B).((not (eq B b Abst)) \to (\forall (u2: T).(\forall (v2: T).(\forall (x: T).((pr0 u2 x) \to ((pr0 v2 x) \to (\forall (t2: T).(\forall (t5: T).(\forall (x0: T).((pr0 t2 x0) \to ((pr0 t5 x0) \to (\forall (u5: T).(\forall (u3: T).(\forall (x1: T).((pr0 u5 x1) \to ((pr0 u3 x1) \to (ex2 T (\lambda (t: T).(pr0 (THead (Flat Appl) u2 (THead (Bind b) u5 t2)) t)) (\lambda (t: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t5)) t))))))))))))))))))) .

axiom pr0_confluence__pr0_cong_upsilon_delta: (not (eq B Abbr Abst)) \to (\forall (u5: T).(\forall (t2: T).(\forall (w: T).((subst0 O u5 t2 w) \to (\forall (u2: T).(\forall (v2: T).(\forall (x: T).((pr0 u2 x) \to ((pr0 v2 x) \to (\forall (t5: T).(\forall (x0: T).((pr0 t2 x0) \to ((pr0 t5 x0) \to (\forall (u3: T).(\forall (x1: T).((pr0 u5 x1) \to ((pr0 u3 x1) \to (ex2 T (\lambda (t: T).(pr0 (THead (Flat Appl) u2 (THead (Bind Abbr) u5 w)) t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) u3 (THead (Flat Appl) (lift (S O) O v2) t5)) t)))))))))))))))))))) .

axiom pr0_confluence__pr0_cong_upsilon_zeta: \forall (b: B).((not (eq B b Abst)) \to (\forall (u0: T).(\forall (u3: T).((pr0 u0 u3) \to (\forall (u2: T).(\forall (v2: T).(\forall (x0: T).((pr0 u2 x0) \to ((pr0 v2 x0) \to (\forall (x: T).(\forall (t3: T).(\forall (x1: T).((pr0 x x1) \to ((pr0 t3 x1) \to (ex2 T (\lambda (t: T).(pr0 (THead (Flat Appl) u2 t3) t)) (\lambda (t: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) (lift (S O) O x))) t))))))))))))))))) .

axiom pr0_confluence__pr0_cong_delta: \forall (u3: T).(\forall (t5: T).(\forall (w: T).((subst0 O u3 t5 w) \to (\forall (u2: T).(\forall (x: T).((pr0 u2 x) \to ((pr0 u3 x) \to (\forall (t3: T).(\forall (x0: T).((pr0 t3 x0) \to ((pr0 t5 x0) \to (ex2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 t3) t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) u3 w) t)))))))))))))) .

axiom pr0_confluence__pr0_upsilon_upsilon: \forall (b: B).((not (eq B b Abst)) \to (\forall (v1: T).(\forall (v2: T).(\forall (x0: T).((pr0 v1 x0) \to ((pr0 v2 x0) \to (\forall (u1: T).(\forall (u2: T).(\forall (x1: T).((pr0 u1 x1) \to ((pr0 u2 x1) \to (\forall (t1: T).(\forall (t2: T).(\forall (x2: T).((pr0 t1 x2) \to ((pr0 t2 x2) \to (ex2 T (\lambda (t: T).(pr0 (THead (Bind b) u1 (THead (Flat Appl) (lift (S O) O v1) t1)) t)) (\lambda (t: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2)) t))))))))))))))))))) .

axiom pr0_confluence__pr0_delta_delta: \forall (u2: T).(\forall (t3: T).(\forall (w: T).((subst0 O u2 t3 w) \to (\forall (u3: T).(\forall (t5: T).(\forall (w0: T).((subst0 O u3 t5 w0) \to (\forall (x: T).((pr0 u2 x) \to ((pr0 u3 x) \to (\forall (x0: T).((pr0 t3 x0) \to ((pr0 t5 x0) \to (ex2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) u3 w0) t)))))))))))))))) .

axiom pr0_confluence__pr0_delta_epsilon: \forall (u2: T).(\forall (t3: T).(\forall (w: T).((subst0 O u2 t3 w) \to (\forall (t4: T).((pr0 (lift (S O) O t4) t3) \to (\forall (t2: T).(ex2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda (t: T).(pr0 t2 t))))))))) .

axiom pr0_confluence: \forall (t0: T).(\forall (t1: T).((pr0 t0 t1) \to (\forall (t2: T).((pr0 t0 t2) \to (ex2 T (\lambda (t: T).(pr0 t1 t)) (\lambda (t: T).(pr0 t2 t))))))) .

axiom pr0_delta1: \forall (u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (w: T).((subst1 O u2 t2 w) \to (pr0 (THead (Bind Abbr) u1 t1) (THead (Bind Abbr) u2 w))))))))) .

axiom pr0_subst1_back: \forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall (i: nat).((subst1 i u2 t1 t2) \to (\forall (u1: T).((pr0 u1 u2) \to (ex2 T (\lambda (t: T).(subst1 i u1 t1 t)) (\lambda (t: T).(pr0 t t2))))))))) .

axiom pr0_subst1_fwd: \forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall (i: nat).((subst1 i u2 t1 t2) \to (\forall (u1: T).((pr0 u2 u1) \to (ex2 T (\lambda (t: T).(subst1 i u1 t1 t)) (\lambda (t: T).(pr0 t2 t))))))))) .

axiom pr0_subst1: \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (v1: T).(\forall (w1: T).(\forall (i: nat).((subst1 i v1 t1 w1) \to (\forall (v2: T).((pr0 v1 v2) \to (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst1 i v2 t2 w2))))))))))) .

axiom nf0_dec: \forall (t1: T).(or (\forall (t2: T).((pr0 t1 t2) \to (eq T t1 t2))) (ex2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 t1 t2)))) .

inductive pr1: T \to (T \to Prop) \def
| pr1_r: \forall (t: T).(pr1 t t)
| pr1_u: \forall (t2: T).(\forall (t1: T).((pr0 t1 t2) \to (\forall (t3: T).((pr1 t2 t3) \to (pr1 t1 t3))))).

axiom pr1_pr0: \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (pr1 t1 t2))) .

axiom pr1_t: \forall (t2: T).(\forall (t1: T).((pr1 t1 t2) \to (\forall (t3: T).((pr1 t2 t3) \to (pr1 t1 t3))))) .

axiom pr1_head_1: \forall (u1: T).(\forall (u2: T).((pr1 u1 u2) \to (\forall (t: T).(\forall (k: K).(pr1 (THead k u1 t) (THead k u2 t)))))) .

axiom pr1_head_2: \forall (t1: T).(\forall (t2: T).((pr1 t1 t2) \to (\forall (u: T).(\forall (k: K).(pr1 (THead k u t1) (THead k u t2)))))) .

axiom pr1_strip: \forall (t0: T).(\forall (t1: T).((pr1 t0 t1) \to (\forall (t2: T).((pr0 t0 t2) \to (ex2 T (\lambda (t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t2 t))))))) .

axiom pr1_confluence: \forall (t0: T).(\forall (t1: T).((pr1 t0 t1) \to (\forall (t2: T).((pr1 t0 t2) \to (ex2 T (\lambda (t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t2 t))))))) .

inductive wcpr0: C \to (C \to Prop) \def
| wcpr0_refl: \forall (c: C).(wcpr0 c c)
| wcpr0_comp: \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (k: K).(wcpr0 (CHead c1 k u1) (CHead c2 k u2)))))))).

axiom wcpr0_gen_sort: \forall (x: C).(\forall (n: nat).((wcpr0 (CSort n) x) \to (eq C x (CSort n)))) .

axiom wcpr0_gen_head: \forall (k: K).(\forall (c1: C).(\forall (x: C).(\forall (u1: T).((wcpr0 (CHead c1 k u1) x) \to (or (eq C x (CHead c1 k u1)) (ex3_2 C T (\lambda (c2: C).(\lambda (u2: T).(eq C x (CHead c2 k u2)))) (\lambda (c2: C).(\lambda (_: T).(wcpr0 c1 c2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2))))))))) .

axiom wcpr0_drop: \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (h: nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((drop h O c1 (CHead e1 k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(drop h O c2 (CHead e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2))))))))))) .

axiom wcpr0_drop_back: \forall (c1: C).(\forall (c2: C).((wcpr0 c2 c1) \to (\forall (h: nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((drop h O c1 (CHead e1 k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(drop h O c2 (CHead e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u2: T).(pr0 u2 u1))))))))))) .

axiom wcpr0_getl: \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (h: nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((getl h c1 (CHead e1 k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(getl h c2 (CHead e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2))))))))))) .

axiom wcpr0_getl_back: \forall (c1: C).(\forall (c2: C).((wcpr0 c2 c1) \to (\forall (h: nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((getl h c1 (CHead e1 k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(getl h c2 (CHead e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u2: T).(pr0 u2 u1))))))))))) .

inductive pr2: C \to (T \to (T \to Prop)) \def
| pr2_free: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (pr2 c t1 t2))))
| pr2_delta: \forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead d (Bind Abbr) u)) \to (\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (t: T).((subst0 i u t2 t) \to (pr2 c t1 t)))))))))).

axiom pr2_gen_sort: \forall (c: C).(\forall (x: T).(\forall (n: nat).((pr2 c (TSort n) x) \to (eq T x (TSort n))))) .

axiom pr2_gen_lref: \forall (c: C).(\forall (x: T).(\forall (n: nat).((pr2 c (TLRef n) x) \to (or (eq T x (TLRef n)) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl n c (CHead d (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq T x (lift (S n) O u))))))))) .

axiom pr2_gen_abst: \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c (THead (Bind Abst) u1 t1) x) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t2)))))))))) .

axiom pr2_gen_cast: \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c (THead (Flat Cast) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr2 c t1 t2)))) (pr2 c t1 x)))))) .

axiom pr2_gen_csort: \forall (t1: T).(\forall (t2: T).(\forall (n: nat).((pr2 (CSort n) t1 t2) \to (pr0 t1 t2)))) .

axiom pr2_gen_ctail: \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall (t2: T).((pr2 (CTail k u c) t1 t2) \to (or (pr2 c t1 t2) (ex3 T (\lambda (_: T).(eq K k (Bind Abbr))) (\lambda (t: T).(pr0 t1 t)) (\lambda (t: T).(subst0 (clen c) u t t2))))))))) .

axiom pr2_thin_dx: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (u: T).(\forall (f: F).(pr2 c (THead (Flat f) u t1) (THead (Flat f) u t2))))))) .

axiom pr2_head_1: \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr2 c u1 u2) \to (\forall (k: K).(\forall (t: T).(pr2 c (THead k u1 t) (THead k u2 t))))))) .

axiom pr2_head_2: \forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u) t1 t2) \to (pr2 c (THead k u t1) (THead k u t2))))))) .

axiom clear_pr2_trans: \forall (c2: C).(\forall (t1: T).(\forall (t2: T).((pr2 c2 t1 t2) \to (\forall (c1: C).((clear c1 c2) \to (pr2 c1 t1 t2)))))) .

axiom pr2_cflat: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (f: F).(\forall (v: T).(pr2 (CHead c (Flat f) v) t1 t2)))))) .

axiom pr2_ctail: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (k: K).(\forall (u: T).(pr2 (CTail k u c) t1 t2)))))) .

axiom pr2_gen_cbind: \forall (b: B).(\forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall (t2: T).((pr2 (CHead c (Bind b) v) t1 t2) \to (pr2 c (THead (Bind b) v t1) (THead (Bind b) v t2))))))) .

axiom pr2_gen_cflat: \forall (f: F).(\forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall (t2: T).((pr2 (CHead c (Flat f) v) t1 t2) \to (pr2 c t1 t2)))))) .

axiom pr2_lift: \forall (c: C).(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to (\forall (t1: T).(\forall (t2: T).((pr2 e t1 t2) \to (pr2 c (lift h d t1) (lift h d t2))))))))) .

axiom pr2_gen_appl: \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c (THead (Flat Appl) u1 t1) x) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr2 c t1 t2)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))))))) .

axiom pr2_gen_abbr: \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c (THead (Bind Abbr) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t2))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 t2))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t2)))))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x))))))))) .

axiom pr2_gen_void: \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c (THead (Bind Void) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t2)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x))))))))) .

axiom pr2_gen_lift: \forall (c: C).(\forall (t1: T).(\forall (x: T).(\forall (h: nat).(\forall (d: nat).((pr2 c (lift h d t1) x) \to (\forall (e: C).((drop h d c e) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(pr2 e t1 t2)))))))))) .

axiom pr2_confluence__pr2_free_free: \forall (c: C).(\forall (t0: T).(\forall (t1: T).(\forall (t2: T).((pr0 t0 t1) \to ((pr0 t0 t2) \to (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t)))))))) .

axiom pr2_confluence__pr2_free_delta: \forall (c: C).(\forall (d: C).(\forall (t0: T).(\forall (t1: T).(\forall (t2: T).(\forall (t4: T).(\forall (u: T).(\forall (i: nat).((pr0 t0 t1) \to ((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 t0 t4) \to ((subst0 i u t4 t2) \to (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t)))))))))))))) .

axiom pr2_confluence__pr2_delta_delta: \forall (c: C).(\forall (d: C).(\forall (d0: C).(\forall (t0: T).(\forall (t1: T).(\forall (t2: T).(\forall (t3: T).(\forall (t4: T).(\forall (u: T).(\forall (u0: T).(\forall (i: nat).(\forall (i0: nat).((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 t0 t3) \to ((subst0 i u t3 t1) \to ((getl i0 c (CHead d0 (Bind Abbr) u0)) \to ((pr0 t0 t4) \to ((subst0 i0 u0 t4 t2) \to (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t)))))))))))))))))))) .

axiom pr2_confluence: \forall (c: C).(\forall (t0: T).(\forall (t1: T).((pr2 c t0 t1) \to (\forall (t2: T).((pr2 c t0 t2) \to (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t)))))))) .

axiom pr2_delta1: \forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead d (Bind Abbr) u)) \to (\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (t: T).((subst1 i u t2 t) \to (pr2 c t1 t)))))))))) .

axiom pr2_subst1: \forall (c: C).(\forall (e: C).(\forall (v: T).(\forall (i: nat).((getl i c (CHead e (Bind Abbr) v)) \to (\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (w1: T).((subst1 i v t1 w1) \to (ex2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v t2 w2)))))))))))) .

axiom pr2_gen_cabbr: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl d c (CHead e (Bind Abbr) u)) \to (\forall (a0: C).((csubst1 d u c a0) \to (\forall (a: C).((drop (S O) d a0 a) \to (\forall (x1: T).((subst1 d u t1 (lift (S O) d x1)) \to (ex2 T (\lambda (x2: T).(subst1 d u t2 (lift (S O) d x2))) (\lambda (x2: T).(pr2 a x1 x2)))))))))))))))) .

inductive pr3 (c:C): T \to (T \to Prop) \def
| pr3_refl: \forall (t: T).(pr3 c t t)
| pr3_sing: \forall (t2: T).(\forall (t1: T).((pr2 c t1 t2) \to (\forall (t3: T).((pr3 c t2 t3) \to (pr3 c t1 t3))))).

axiom pr3_gen_sort: \forall (c: C).(\forall (x: T).(\forall (n: nat).((pr3 c (TSort n) x) \to (eq T x (TSort n))))) .

axiom pr3_gen_abst: \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c (THead (Bind Abst) u1 t1) x) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t1 t2)))))))))) .

axiom pr3_gen_cast: \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c (THead (Flat Cast) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 c t1 t2)))) (pr3 c t1 x)))))) .

axiom clear_pr3_trans: \forall (c2: C).(\forall (t1: T).(\forall (t2: T).((pr3 c2 t1 t2) \to (\forall (c1: C).((clear c1 c2) \to (pr3 c1 t1 t2)))))) .

axiom pr3_pr2: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (pr3 c t1 t2)))) .

axiom pr3_t: \forall (t2: T).(\forall (t1: T).(\forall (c: C).((pr3 c t1 t2) \to (\forall (t3: T).((pr3 c t2 t3) \to (pr3 c t1 t3)))))) .

axiom pr3_thin_dx: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall (u: T).(\forall (f: F).(pr3 c (THead (Flat f) u t1) (THead (Flat f) u t2))))))) .

axiom pr3_head_1: \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u1 u2) \to (\forall (k: K).(\forall (t: T).(pr3 c (THead k u1 t) (THead k u2 t))))))) .

axiom pr3_head_2: \forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pr3 (CHead c k u) t1 t2) \to (pr3 c (THead k u t1) (THead k u t2))))))) .

axiom pr3_head_21: \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u1 u2) \to (\forall (k: K).(\forall (t1: T).(\forall (t2: T).((pr3 (CHead c k u1) t1 t2) \to (pr3 c (THead k u1 t1) (THead k u2 t2))))))))) .

axiom pr3_head_12: \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u1 u2) \to (\forall (k: K).(\forall (t1: T).(\forall (t2: T).((pr3 (CHead c k u2) t1 t2) \to (pr3 c (THead k u1 t1) (THead k u2 t2))))))))) .

axiom pr3_pr1: \forall (t1: T).(\forall (t2: T).((pr1 t1 t2) \to (\forall (c: C).(pr3 c t1 t2)))) .

axiom pr3_cflat: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall (f: F).(\forall (v: T).(pr3 (CHead c (Flat f) v) t1 t2)))))) .

axiom pr3_pr0_pr2_t: \forall (u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (c: C).(\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pr3 (CHead c k u1) t1 t2)))))))) .

axiom pr3_pr2_pr2_t: \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr2 c u1 u2) \to (\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pr3 (CHead c k u1) t1 t2)))))))) .

axiom pr3_pr2_pr3_t: \forall (c: C).(\forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pr3 (CHead c k u2) t1 t2) \to (\forall (u1: T).((pr2 c u1 u2) \to (pr3 (CHead c k u1) t1 t2)))))))) .

axiom pr3_pr3_pr3_t: \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u1 u2) \to (\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pr3 (CHead c k u2) t1 t2) \to (pr3 (CHead c k u1) t1 t2)))))))) .

axiom pr3_lift: \forall (c: C).(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to (\forall (t1: T).(\forall (t2: T).((pr3 e t1 t2) \to (pr3 c (lift h d t1) (lift h d t2))))))))) .

axiom pr3_wcpr0_t: \forall (c1: C).(\forall (c2: C).((wcpr0 c2 c1) \to (\forall (t1: T).(\forall (t2: T).((pr3 c1 t1 t2) \to (pr3 c2 t1 t2)))))) .

axiom pr3_gen_lift: \forall (c: C).(\forall (t1: T).(\forall (x: T).(\forall (h: nat).(\forall (d: nat).((pr3 c (lift h d t1) x) \to (\forall (e: C).((drop h d c e) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(pr3 e t1 t2)))))))))) .

axiom pr3_gen_lref: \forall (c: C).(\forall (x: T).(\forall (n: nat).((pr3 c (TLRef n) x) \to (or (eq T x (TLRef n)) (ex3_3 C T T (\lambda (d: C).(\lambda (u: T).(\lambda (_: T).(getl n c (CHead d (Bind Abbr) u))))) (\lambda (d: C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(eq T x (lift (S n) O v)))))))))) .

axiom pr3_gen_void: \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c (THead (Bind Void) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t1 t2)))))) (pr3 (CHead c (Bind Void) u1) t1 (lift (S O) O x))))))) .

axiom pr3_gen_abbr: \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c (THead (Bind Abbr) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Abbr) u1) t1 t2)))) (pr3 (CHead c (Bind Abbr) u1) t1 (lift (S O) O x))))))) .

axiom pr3_gen_appl: \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c (THead (Flat Appl) u1 t1) x) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 c t1 t2)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u2 t2) x))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) x))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))))))) .

axiom pr3_strip: \forall (c: C).(\forall (t0: T).(\forall (t1: T).((pr3 c t0 t1) \to (\forall (t2: T).((pr2 c t0 t2) \to (ex2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)))))))) .

axiom pr3_confluence: \forall (c: C).(\forall (t0: T).(\forall (t1: T).((pr3 c t0 t1) \to (\forall (t2: T).((pr3 c t0 t2) \to (ex2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)))))))) .

axiom pr3_subst1: \forall (c: C).(\forall (e: C).(\forall (v: T).(\forall (i: nat).((getl i c (CHead e (Bind Abbr) v)) \to (\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall (w1: T).((subst1 i v t1 w1) \to (ex2 T (\lambda (w2: T).(pr3 c w1 w2)) (\lambda (w2: T).(subst1 i v t2 w2)))))))))))) .

axiom pr3_gen_cabbr: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl d c (CHead e (Bind Abbr) u)) \to (\forall (a0: C).((csubst1 d u c a0) \to (\forall (a: C).((drop (S O) d a0 a) \to (\forall (x1: T).((subst1 d u t1 (lift (S O) d x1)) \to (ex2 T (\lambda (x2: T).(subst1 d u t2 (lift (S O) d x2))) (\lambda (x2: T).(pr3 a x1 x2)))))))))))))))) .

axiom pr3_iso_appls_cast: \forall (c: C).(\forall (v: T).(\forall (t: T).(\forall (vs: TList).(let u1 \def (THeads (Flat Appl) vs (THead (Flat Cast) v t)) in (\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to (pr3 c (THeads (Flat Appl) vs t) u2)))))))) .

inductive csuba (g:G): C \to (C \to Prop) \def
| csuba_sort: \forall (n: nat).(csuba g (CSort n) (CSort n))
| csuba_head: \forall (c1: C).(\forall (c2: C).((csuba g c1 c2) \to (\forall (k: K).(\forall (u: T).(csuba g (CHead c1 k u) (CHead c2 k u))))))
| csuba_abst: \forall (c1: C).(\forall (c2: C).((csuba g c1 c2) \to (\forall (t: T).(\forall (a: A).((arity g c1 t (asucc g a)) \to (\forall (u: T).((arity g c2 u a) \to (csuba g (CHead c1 (Bind Abst) t) (CHead c2 (Bind Abbr) u))))))))).

axiom csuba_gen_abbr: \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u: T).((csuba g (CHead d1 (Bind Abbr) u) c) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))))))) .

axiom csuba_gen_void: \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u: T).((csuba g (CHead d1 (Bind Void) u) c) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d1 d2))))))) .

axiom csuba_gen_abst: \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u1: T).((csuba g (CHead d1 (Bind Abst) u1) c) \to (or (ex2 C (\lambda (d2: C).(eq C c (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))))))) .

axiom csuba_gen_flat: \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u1: T).(\forall (f: F).((csuba g (CHead d1 (Flat f) u1) c) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d1 d2))))))))) .

axiom csuba_gen_bind: \forall (g: G).(\forall (b1: B).(\forall (e1: C).(\forall (c2: C).(\forall (v1: T).((csuba g (CHead e1 (Bind b1) v1) c2) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 e2)))))))))) .

axiom csuba_refl: \forall (g: G).(\forall (c: C).(csuba g c c)) .

axiom csuba_clear_conf: \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csuba g c1 c2) \to (\forall (e1: C).((clear c1 e1) \to (ex2 C (\lambda (e2: C).(csuba g e1 e2)) (\lambda (e2: C).(clear c2 e2)))))))) .

axiom csuba_drop_abbr: \forall (i: nat).(\forall (c1: C).(\forall (d1: C).(\forall (u: T).((drop i O c1 (CHead d1 (Bind Abbr) u)) \to (\forall (g: G).(\forall (c2: C).((csuba g c1 c2) \to (ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))))))))) .

axiom csuba_drop_abst: \forall (i: nat).(\forall (c1: C).(\forall (d1: C).(\forall (u1: T).((drop i O c1 (CHead d1 (Bind Abst) u1)) \to (\forall (g: G).(\forall (c2: C).((csuba g c1 c2) \to (or (ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop i O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))))))))))) .

axiom csuba_getl_abbr: \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (u: T).(\forall (i: nat).((getl i c1 (CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).((csuba g c1 c2) \to (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))))))))) .

axiom csuba_getl_abst: \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (u1: T).(\forall (i: nat).((getl i c1 (CHead d1 (Bind Abst) u1)) \to (\forall (c2: C).((csuba g c1 c2) \to (or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))))))))))) .

axiom csuba_arity: \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).((arity g c1 t a) \to (\forall (c2: C).((csuba g c1 c2) \to (arity g c2 t a))))))) .

axiom csuba_arity_rev: \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).((arity g c1 t a) \to (\forall (c2: C).((csuba g c2 c1) \to (arity g c2 t a))))))) .

axiom arity_appls_appl: \forall (g: G).(\forall (c: C).(\forall (v: T).(\forall (a1: A).((arity g c v a1) \to (\forall (u: T).((arity g c u (asucc g a1)) \to (\forall (t: T).(\forall (vs: TList).(\forall (a2: A).((arity g c (THeads (Flat Appl) vs (THead (Bind Abbr) v t)) a2) \to (arity g c (THeads (Flat Appl) vs (THead (Flat Appl) v (THead (Bind Abst) u t))) a2))))))))))) .

axiom arity_sred_wcpr0_pr0: \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (a: A).((arity g c1 t1 a) \to (\forall (c2: C).((wcpr0 c1 c2) \to (\forall (t2: T).((pr0 t1 t2) \to (arity g c2 t2 a))))))))) .

axiom arity_sred_wcpr0_pr1: \forall (t1: T).(\forall (t2: T).((pr1 t1 t2) \to (\forall (g: G).(\forall (c1: C).(\forall (a: A).((arity g c1 t1 a) \to (\forall (c2: C).((wcpr0 c1 c2) \to (arity g c2 t2 a))))))))) .

axiom arity_sred_pr2: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (g: G).(\forall (a: A).((arity g c t1 a) \to (arity g c t2 a))))))) .

axiom arity_sred_pr3: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall (g: G).(\forall (a: A).((arity g c t1 a) \to (arity g c t2 a))))))) .

definition nf2: C \to (T \to Prop) \def \lambda (c: C).(\lambda (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (eq T t1 t2)))).

axiom nf2_gen_base__aux: \forall (k: K).(\forall (t: T).(\forall (u: T).((eq T (THead k u t) t) \to (\forall (P: Prop).P)))) .

axiom nf2_gen_lref: \forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead d (Bind Abbr) u)) \to ((nf2 c (TLRef i)) \to (\forall (P: Prop).P)))))) .

axiom nf2_gen_abst: \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Bind Abst) u t)) \to (land (nf2 c u) (nf2 (CHead c (Bind Abst) u) t))))) .

axiom nf2_gen_cast: \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Flat Cast) u t)) \to (\forall (P: Prop).P)))) .

axiom nf2_gen_flat: \forall (f: F).(\forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Flat f) u t)) \to (land (nf2 c u) (nf2 c t)))))) .

axiom nf2_sort: \forall (c: C).(\forall (n: nat).(nf2 c (TSort n))) .

axiom nf2_abst: \forall (c: C).(\forall (u: T).((nf2 c u) \to (\forall (b: B).(\forall (v: T).(\forall (t: T).((nf2 (CHead c (Bind b) v) t) \to (nf2 c (THead (Bind Abst) u t)))))))) .

axiom nf2_pr3_unfold: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to ((nf2 c t1) \to (eq T t1 t2))))) .

axiom nf2_pr3_confluence: \forall (c: C).(\forall (t1: T).((nf2 c t1) \to (\forall (t2: T).((nf2 c t2) \to (\forall (t: T).((pr3 c t t1) \to ((pr3 c t t2) \to (eq T t1 t2)))))))) .

axiom nf2_appl_lref: \forall (c: C).(\forall (u: T).((nf2 c u) \to (\forall (i: nat).((nf2 c (TLRef i)) \to (nf2 c (THead (Flat Appl) u (TLRef i))))))) .

axiom nf2_lref_abst: \forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead e (Bind Abst) u)) \to (nf2 c (TLRef i)))))) .

axiom nf2_lift: \forall (d: C).(\forall (t: T).((nf2 d t) \to (\forall (c: C).(\forall (h: nat).(\forall (i: nat).((drop h i c d) \to (nf2 c (lift h i t)))))))) .

axiom nf2_lift1: \forall (e: C).(\forall (hds: PList).(\forall (c: C).(\forall (t: T).((drop1 hds c e) \to ((nf2 e t) \to (nf2 c (lift1 hds t))))))) .

axiom nf2_iso_appls_lref: \forall (c: C).(\forall (i: nat).((nf2 c (TLRef i)) \to (\forall (vs: TList).(\forall (u: T).((pr3 c (THeads (Flat Appl) vs (TLRef i)) u) \to (iso (THeads (Flat Appl) vs (TLRef i)) u)))))) .

axiom nf2_dec: \forall (c: C).(\forall (t1: T).(or (nf2 c t1) (ex2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 c t1 t2))))) .

inductive sn3 (c:C): T \to Prop \def
| sn3_sing: \forall (t1: T).(((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2))))) \to (sn3 c t1)).

definition sns3: C \to (TList \to Prop) \def let rec sns3 (c: C) (ts: TList): Prop \def (match ts with [TNil \Rightarrow True | (TCons t ts0) \Rightarrow (land (sn3 c t) (sns3 c ts0))]) in sns3.

axiom sn3_gen_flat: \forall (f: F).(\forall (c: C).(\forall (u: T).(\forall (t: T).((sn3 c (THead (Flat f) u t)) \to (land (sn3 c u) (sn3 c t)))))) .

axiom sn3_nf2: \forall (c: C).(\forall (t: T).((nf2 c t) \to (sn3 c t))) .

axiom sn3_pr3_trans: \forall (c: C).(\forall (t1: T).((sn3 c t1) \to (\forall (t2: T).((pr3 c t1 t2) \to (sn3 c t2))))) .

axiom sn3_pr2_intro: \forall (c: C).(\forall (t1: T).(((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr2 c t1 t2) \to (sn3 c t2))))) \to (sn3 c t1))) .

axiom sn3_cast: \forall (c: C).(\forall (u: T).((sn3 c u) \to (\forall (t: T).((sn3 c t) \to (sn3 c (THead (Flat Cast) u t)))))) .

axiom nf2_sn3: \forall (c: C).(\forall (t: T).((sn3 c t) \to (ex2 T (\lambda (u: T).(pr3 c t u)) (\lambda (u: T).(nf2 c u))))) .

axiom sn3_appl_lref: \forall (c: C).(\forall (i: nat).((nf2 c (TLRef i)) \to (\forall (v: T).((sn3 c v) \to (sn3 c (THead (Flat Appl) v (TLRef i))))))) .

axiom sn3_appl_cast: \forall (c: C).(\forall (v: T).(\forall (u: T).((sn3 c (THead (Flat Appl) v u)) \to (\forall (t: T).((sn3 c (THead (Flat Appl) v t)) \to (sn3 c (THead (Flat Appl) v (THead (Flat Cast) u t)))))))) .

axiom sn3_appl_appl: \forall (v1: T).(\forall (t1: T).(let u1 \def (THead (Flat Appl) v1 t1) in (\forall (c: C).((sn3 c u1) \to (\forall (v2: T).((sn3 c v2) \to (((\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) v2 u2)))))) \to (sn3 c (THead (Flat Appl) v2 u1))))))))) .

axiom sn3_appl_appls: \forall (v1: T).(\forall (t1: T).(\forall (vs: TList).(let u1 \def (THeads (Flat Appl) (TCons v1 vs) t1) in (\forall (c: C).((sn3 c u1) \to (\forall (v2: T).((sn3 c v2) \to (((\forall (u2: T).((pr3 c u1 u2) \to ((((iso u1 u2) \to (\forall (P: Prop).P))) \to (sn3 c (THead (Flat Appl) v2 u2)))))) \to (sn3 c (THead (Flat Appl) v2 u1)))))))))) .

axiom sn3_appls_lref: \forall (c: C).(\forall (i: nat).((nf2 c (TLRef i)) \to (\forall (us: TList).((sns3 c us) \to (sn3 c (THeads (Flat Appl) us (TLRef i))))))) .

axiom sn3_appls_cast: \forall (c: C).(\forall (vs: TList).(\forall (u: T).((sn3 c (THeads (Flat Appl) vs u)) \to (\forall (t: T).((sn3 c (THeads (Flat Appl) vs t)) \to (sn3 c (THeads (Flat Appl) vs (THead (Flat Cast) u t)))))))) .

axiom sn3_lift: \forall (d: C).(\forall (t: T).((sn3 d t) \to (\forall (c: C).(\forall (h: nat).(\forall (i: nat).((drop h i c d) \to (sn3 c (lift h i t)))))))) .

axiom sn3_abbr: \forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: nat).((getl i c (CHead d (Bind Abbr) v)) \to ((sn3 d v) \to (sn3 c (TLRef i))))))) .

axiom sns3_lifts: \forall (c: C).(\forall (d: C).(\forall (h: nat).(\forall (i: nat).((drop h i c d) \to (\forall (ts: TList).((sns3 d ts) \to (sns3 c (lifts h i ts)))))))) .

axiom sns3_lifts1: \forall (e: C).(\forall (hds: PList).(\forall (c: C).((drop1 hds c e) \to (\forall (ts: TList).((sns3 e ts) \to (sns3 c (lifts1 hds ts))))))) .

axiom sn3_gen_lift: \forall (c1: C).(\forall (t: T).(\forall (h: nat).(\forall (d: nat).((sn3 c1 (lift h d t)) \to (\forall (c2: C).((drop h d c1 c2) \to (sn3 c2 t))))))) .

definition sc3: G \to (A \to (C \to (T \to Prop))) \def let rec sc3 (g: G) (a: A): (C \to (T \to Prop)) \def (\lambda (c: C).(\lambda (t: T).(match a with [(ASort h n) \Rightarrow (land (arity g c t (ASort h n)) (sn3 c t)) | (AHead a1 a2) \Rightarrow (land (arity g c t (AHead a1 a2)) (\forall (d: C).(\forall (w: T).((sc3 g a1 d w) \to (\forall (is: PList).((drop1 is d c) \to (sc3 g a2 d (THead (Flat Appl) w (lift1 is t)))))))))]))) in sc3.

axiom sc3_arity_gen: \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((sc3 g a c t) \to (arity g c t a))))) .

axiom sc3_repl: \forall (g: G).(\forall (a1: A).(\forall (c: C).(\forall (t: T).((sc3 g a1 c t) \to (\forall (a2: A).((leq g a1 a2) \to (sc3 g a2 c t))))))) .

axiom sc3_lift: \forall (g: G).(\forall (a: A).(\forall (e: C).(\forall (t: T).((sc3 g a e t) \to (\forall (c: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to (sc3 g a c (lift h d t)))))))))) .

axiom sc3_lift1: \forall (g: G).(\forall (e: C).(\forall (a: A).(\forall (hds: PList).(\forall (c: C).(\forall (t: T).((sc3 g a e t) \to ((drop1 hds c e) \to (sc3 g a c (lift1 hds t))))))))) .

axiom sc3_abbr: \forall (g: G).(\forall (a: A).(\forall (vs: TList).(\forall (i: nat).(\forall (d: C).(\forall (v: T).(\forall (c: C).((sc3 g a c (THeads (Flat Appl) vs (lift (S i) O v))) \to ((getl i c (CHead d (Bind Abbr) v)) \to (sc3 g a c (THeads (Flat Appl) vs (TLRef i))))))))))) .

axiom sc3_cast: \forall (g: G).(\forall (a: A).(\forall (vs: TList).(\forall (c: C).(\forall (u: T).((sc3 g (asucc g a) c (THeads (Flat Appl) vs u)) \to (\forall (t: T).((sc3 g a c (THeads (Flat Appl) vs t)) \to (sc3 g a c (THeads (Flat Appl) vs (THead (Flat Cast) u t)))))))))) .

axiom sc3_bind: \forall (g: G).(\forall (b: B).((not (eq B b Abst)) \to (\forall (a1: A).(\forall (a2: A).(\forall (vs: TList).(\forall (c: C).(\forall (v: T).(\forall (t: T).((sc3 g a2 (CHead c (Bind b) v) (THeads (Flat Appl) (lifts (S O) O vs) t)) \to ((sc3 g a1 c v) \to (sc3 g a2 c (THeads (Flat Appl) vs (THead (Bind b) v t))))))))))))) .

axiom sc3_appl: \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (vs: TList).(\forall (c: C).(\forall (v: T).(\forall (t: T).((sc3 g a2 c (THeads (Flat Appl) vs (THead (Bind Abbr) v t))) \to ((sc3 g a1 c v) \to (\forall (w: T).((sc3 g (asucc g a1) c w) \to (sc3 g a2 c (THeads (Flat Appl) vs (THead (Flat Appl) v (THead (Bind Abst) w t)))))))))))))) .

axiom sc3_props__sc3_sn3_abst: \forall (g: G).(\forall (a: A).(land (\forall (c: C).(\forall (t: T).((sc3 g a c t) \to (sn3 c t)))) (\forall (vs: TList).(\forall (i: nat).(let t \def (THeads (Flat Appl) vs (TLRef i)) in (\forall (c: C).((arity g c t a) \to ((nf2 c (TLRef i)) \to ((sns3 c vs) \to (sc3 g a c t)))))))))) .

axiom sc3_sn3: \forall (g: G).(\forall (a: A).(\forall (c: C).(\forall (t: T).((sc3 g a c t) \to (sn3 c t))))) .

axiom sc3_abst: \forall (g: G).(\forall (a: A).(\forall (vs: TList).(\forall (c: C).(\forall (i: nat).((arity g c (THeads (Flat Appl) vs (TLRef i)) a) \to ((nf2 c (TLRef i)) \to ((sns3 c vs) \to (sc3 g a c (THeads (Flat Appl) vs (TLRef i)))))))))) .

inductive csubc (g:G): C \to (C \to Prop) \def
| csubc_sort: \forall (n: nat).(csubc g (CSort n) (CSort n))
| csubc_head: \forall (c1: C).(\forall (c2: C).((csubc g c1 c2) \to (\forall (k: K).(\forall (v: T).(csubc g (CHead c1 k v) (CHead c2 k v))))))
| csubc_abst: \forall (c1: C).(\forall (c2: C).((csubc g c1 c2) \to (\forall (v: T).(\forall (a: A).((sc3 g (asucc g a) c1 v) \to (\forall (w: T).((sc3 g a c2 w) \to (csubc g (CHead c1 (Bind Abst) v) (CHead c2 (Bind Abbr) w))))))))).

definition ceqc: G \to (C \to (C \to Prop)) \def \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(or (csubc g c1 c2) (csubc g c2 c1)))).

axiom scubc_refl: \forall (g: G).(\forall (c: C).(csubc g c c)) .

axiom ceqc_sym: \forall (g: G).(\forall (c1: C).(\forall (c2: C).((ceqc g c1 c2) \to (ceqc g c2 c1)))) .

axiom drop_csubc_trans: \forall (g: G).(\forall (c2: C).(\forall (e2: C).(\forall (d: nat).(\forall (h: nat).((drop h d c2 e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C (\lambda (c1: C).(drop h d c1 e1)) (\lambda (c1: C).(csubc g c2 c1)))))))))) .

axiom csubc_drop_conf_rev: \forall (g: G).(\forall (c2: C).(\forall (e2: C).(\forall (d: nat).(\forall (h: nat).((drop h d c2 e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C (\lambda (c1: C).(drop h d c1 e1)) (\lambda (c1: C).(csubc g c1 c2)))))))))) .

axiom drop1_csubc_trans: \forall (g: G).(\forall (hds: PList).(\forall (c2: C).(\forall (e2: C).((drop1 hds c2 e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C (\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(csubc g c2 c1))))))))) .

axiom csubc_drop1_conf_rev: \forall (g: G).(\forall (hds: PList).(\forall (c2: C).(\forall (e2: C).((drop1 hds c2 e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C (\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(csubc g c1 c2))))))))) .

axiom drop1_ceqc_trans: \forall (g: G).(\forall (hds: PList).(\forall (c2: C).(\forall (e2: C).((drop1 hds c2 e2) \to (\forall (e1: C).((ceqc g e2 e1) \to (ex2 C (\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(ceqc g c2 c1))))))))) .

axiom sc3_ceqc_trans: \forall (g: G).(\forall (a: A).(\forall (vs: TList).(\forall (c1: C).(\forall (t: T).((sc3 g a c1 (THeads (Flat Appl) vs t)) \to (\forall (c2: C).((ceqc g c2 c1) \to (sc3 g a c2 (THeads (Flat Appl) vs t))))))))) .

axiom sc3_arity: \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t a) \to (sc3 g a c t))))) .

definition pc1: T \to (T \to Prop) \def \lambda (t1: T).(\lambda (t2: T).(ex2 T (\lambda (t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t2 t)))).

axiom pc1_pr0_r: \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (pc1 t1 t2))) .

axiom pc1_pr0_x: \forall (t1: T).(\forall (t2: T).((pr0 t2 t1) \to (pc1 t1 t2))) .

axiom pc1_pr0_u: \forall (t2: T).(\forall (t1: T).((pr0 t1 t2) \to (\forall (t3: T).((pc1 t2 t3) \to (pc1 t1 t3))))) .

axiom pc1_refl: \forall (t: T).(pc1 t t) .

axiom pc1_s: \forall (t2: T).(\forall (t1: T).((pc1 t1 t2) \to (pc1 t2 t1))) .

axiom pc1_head_1: \forall (u1: T).(\forall (u2: T).((pc1 u1 u2) \to (\forall (t: T).(\forall (k: K).(pc1 (THead k u1 t) (THead k u2 t)))))) .

axiom pc1_head_2: \forall (t1: T).(\forall (t2: T).((pc1 t1 t2) \to (\forall (u: T).(\forall (k: K).(pc1 (THead k u t1) (THead k u t2)))))) .

axiom pc1_t: \forall (t2: T).(\forall (t1: T).((pc1 t1 t2) \to (\forall (t3: T).((pc1 t2 t3) \to (pc1 t1 t3))))) .

axiom pc1_pr0_u2: \forall (t0: T).(\forall (t1: T).((pr0 t0 t1) \to (\forall (t2: T).((pc1 t0 t2) \to (pc1 t1 t2))))) .

axiom pc1_head: \forall (u1: T).(\forall (u2: T).((pc1 u1 u2) \to (\forall (t1: T).(\forall (t2: T).((pc1 t1 t2) \to (\forall (k: K).(pc1 (THead k u1 t1) (THead k u2 t2)))))))) .

definition pc3: C \to (T \to (T \to Prop)) \def \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(ex2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t))))).

axiom clear_pc3_trans: \forall (c2: C).(\forall (t1: T).(\forall (t2: T).((pc3 c2 t1 t2) \to (\forall (c1: C).((clear c1 c2) \to (pc3 c1 t1 t2)))))) .

axiom pc3_pr2_r: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (pc3 c t1 t2)))) .

axiom pc3_pr2_x: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t2 t1) \to (pc3 c t1 t2)))) .

axiom pc3_pr3_r: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (pc3 c t1 t2)))) .

axiom pc3_pr3_x: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t2 t1) \to (pc3 c t1 t2)))) .

axiom pc3_pr3_t: \forall (c: C).(\forall (t1: T).(\forall (t0: T).((pr3 c t1 t0) \to (\forall (t2: T).((pr3 c t2 t0) \to (pc3 c t1 t2)))))) .

axiom pc3_pr2_u: \forall (c: C).(\forall (t2: T).(\forall (t1: T).((pr2 c t1 t2) \to (\forall (t3: T).((pc3 c t2 t3) \to (pc3 c t1 t3)))))) .

axiom pc3_refl: \forall (c: C).(\forall (t: T).(pc3 c t t)) .

axiom pc3_s: \forall (c: C).(\forall (t2: T).(\forall (t1: T).((pc3 c t1 t2) \to (pc3 c t2 t1)))) .

axiom pc3_thin_dx: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3 c t1 t2) \to (\forall (u: T).(\forall (f: F).(pc3 c (THead (Flat f) u t1) (THead (Flat f) u t2))))))) .

axiom pc3_head_1: \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pc3 c u1 u2) \to (\forall (k: K).(\forall (t: T).(pc3 c (THead k u1 t) (THead k u2 t))))))) .

axiom pc3_head_2: \forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pc3 (CHead c k u) t1 t2) \to (pc3 c (THead k u t1) (THead k u t2))))))) .

axiom pc3_pc1: \forall (t1: T).(\forall (t2: T).((pc1 t1 t2) \to (\forall (c: C).(pc3 c t1 t2)))) .

axiom pc3_t: \forall (t2: T).(\forall (c: C).(\forall (t1: T).((pc3 c t1 t2) \to (\forall (t3: T).((pc3 c t2 t3) \to (pc3 c t1 t3)))))) .

axiom pc3_pr2_u2: \forall (c: C).(\forall (t0: T).(\forall (t1: T).((pr2 c t0 t1) \to (\forall (t2: T).((pc3 c t0 t2) \to (pc3 c t1 t2)))))) .

axiom pc3_head_12: \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pc3 c u1 u2) \to (\forall (k: K).(\forall (t1: T).(\forall (t2: T).((pc3 (CHead c k u2) t1 t2) \to (pc3 c (THead k u1 t1) (THead k u2 t2))))))))) .

axiom pc3_head_21: \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pc3 c u1 u2) \to (\forall (k: K).(\forall (t1: T).(\forall (t2: T).((pc3 (CHead c k u1) t1 t2) \to (pc3 c (THead k u1 t1) (THead k u2 t2))))))))) .

axiom pc3_pr0_pr2_t: \forall (u1: T).(\forall (u2: T).((pr0 u2 u1) \to (\forall (c: C).(\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pc3 (CHead c k u1) t1 t2)))))))) .

axiom pc3_pr2_pr2_t: \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr2 c u2 u1) \to (\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pc3 (CHead c k u1) t1 t2)))))))) .

axiom pc3_pr2_pr3_t: \forall (c: C).(\forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pr3 (CHead c k u2) t1 t2) \to (\forall (u1: T).((pr2 c u2 u1) \to (pc3 (CHead c k u1) t1 t2)))))))) .

axiom pc3_pr3_pc3_t: \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u2 u1) \to (\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pc3 (CHead c k u2) t1 t2) \to (pc3 (CHead c k u1) t1 t2)))))))) .

axiom pc3_lift: \forall (c: C).(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to (\forall (t1: T).(\forall (t2: T).((pc3 e t1 t2) \to (pc3 c (lift h d t1) (lift h d t2))))))))) .

axiom pc3_wcpr0__pc3_wcpr0_t_aux: \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (k: K).(\forall (u: T).(\forall (t1: T).(\forall (t2: T).((pr3 (CHead c1 k u) t1 t2) \to (pc3 (CHead c2 k u) t1 t2)))))))) .

axiom pc3_wcpr0_t: \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (t1: T).(\forall (t2: T).((pr3 c1 t1 t2) \to (pc3 c2 t1 t2)))))) .

axiom pc3_wcpr0: \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (t1: T).(\forall (t2: T).((pc3 c1 t1 t2) \to (pc3 c2 t1 t2)))))) .

inductive pc3_left (c:C): T \to (T \to Prop) \def
| pc3_left_r: \forall (t: T).(pc3_left c t t)
| pc3_left_ur: \forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (t3: T).((pc3_left c t2 t3) \to (pc3_left c t1 t3)))))
| pc3_left_ux: \forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (t3: T).((pc3_left c t1 t3) \to (pc3_left c t2 t3))))).

axiom pc3_ind_left__pc3_left_pr3: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (pc3_left c t1 t2)))) .

axiom pc3_ind_left__pc3_left_trans: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3_left c t1 t2) \to (\forall (t3: T).((pc3_left c t2 t3) \to (pc3_left c t1 t3)))))) .

axiom pc3_ind_left__pc3_left_sym: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3_left c t1 t2) \to (pc3_left c t2 t1)))) .

axiom pc3_ind_left__pc3_left_pc3: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3 c t1 t2) \to (pc3_left c t1 t2)))) .

axiom pc3_ind_left__pc3_pc3_left: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3_left c t1 t2) \to (pc3 c t1 t2)))) .

axiom pc3_ind_left: \forall (c: C).(\forall (P: ((T \to (T \to Prop)))).(((\forall (t: T).(P t t))) \to (((\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (t3: T).((pc3 c t2 t3) \to ((P t2 t3) \to (P t1 t3)))))))) \to (((\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (t3: T).((pc3 c t1 t3) \to ((P t1 t3) \to (P t2 t3)))))))) \to (\forall (t: T).(\forall (t0: T).((pc3 c t t0) \to (P t t0)))))))) .

axiom pc3_gen_sort: \forall (c: C).(\forall (m: nat).(\forall (n: nat).((pc3 c (TSort m) (TSort n)) \to (eq nat m n)))) .

axiom pc3_gen_abst: \forall (c: C).(\forall (u1: T).(\forall (u2: T).(\forall (t1: T).(\forall (t2: T).((pc3 c (THead (Bind Abst) u1 t1) (THead (Bind Abst) u2 t2)) \to (land (pc3 c u1 u2) (\forall (b: B).(\forall (u: T).(pc3 (CHead c (Bind b) u) t1 t2))))))))) .

axiom pc3_gen_lift: \forall (c: C).(\forall (t1: T).(\forall (t2: T).(\forall (h: nat).(\forall (d: nat).((pc3 c (lift h d t1) (lift h d t2)) \to (\forall (e: C).((drop h d c e) \to (pc3 e t1 t2)))))))) .

axiom pc3_gen_not_abst: \forall (b: B).((not (eq B b Abst)) \to (\forall (c: C).(\forall (t1: T).(\forall (t2: T).(\forall (u1: T).(\forall (u2: T).((pc3 c (THead (Bind b) u1 t1) (THead (Bind Abst) u2 t2)) \to (pc3 (CHead c (Bind b) u1) t1 (lift (S O) O (THead (Bind Abst) u2 t2)))))))))) .

axiom pc3_gen_lift_abst: \forall (c: C).(\forall (t: T).(\forall (t2: T).(\forall (u2: T).(\forall (h: nat).(\forall (d: nat).((pc3 c (lift h d t) (THead (Bind Abst) u2 t2)) \to (\forall (e: C).((drop h d c e) \to (ex3_2 T T (\lambda (u1: T).(\lambda (t1: T).(pr3 e t (THead (Bind Abst) u1 t1)))) (\lambda (u1: T).(\lambda (_: T).(pr3 c u2 (lift h d u1)))) (\lambda (_: T).(\lambda (t1: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t2 (lift h (S d) t1))))))))))))))) .

axiom pc3_pr2_fsubst0: \forall (c1: C).(\forall (t1: T).(\forall (t: T).((pr2 c1 t1 t) \to (\forall (i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t2: T).((fsubst0 i u c1 t1 c2 t2) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 c2 t2 t))))))))))) .

axiom pc3_pr2_fsubst0_back: \forall (c1: C).(\forall (t: T).(\forall (t1: T).((pr2 c1 t t1) \to (\forall (i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t2: T).((fsubst0 i u c1 t1 c2 t2) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 c2 t t2))))))))))) .

axiom pc3_fsubst0: \forall (c1: C).(\forall (t1: T).(\forall (t: T).((pc3 c1 t1 t) \to (\forall (i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t2: T).((fsubst0 i u c1 t1 c2 t2) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 c2 t2 t))))))))))) .

axiom pc3_gen_cabbr: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3 c t1 t2) \to (\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl d c (CHead e (Bind Abbr) u)) \to (\forall (a0: C).((csubst1 d u c a0) \to (\forall (a: C).((drop (S O) d a0 a) \to (\forall (x1: T).((subst1 d u t1 (lift (S O) d x1)) \to (\forall (x2: T).((subst1 d u t2 (lift (S O) d x2)) \to (pc3 a x1 x2)))))))))))))))) .

inductive ty3 (g:G): C \to (T \to (T \to Prop)) \def
| ty3_conv: \forall (c: C).(\forall (t2: T).(\forall (t: T).((ty3 g c t2 t) \to (\forall (u: T).(\forall (t1: T).((ty3 g c u t1) \to ((pc3 c t1 t2) \to (ty3 g c u t2))))))))
| ty3_sort: \forall (c: C).(\forall (m: nat).(ty3 g c (TSort m) (TSort (next g m))))
| ty3_abbr: \forall (n: nat).(\forall (c: C).(\forall (d: C).(\forall (u: T).((getl n c (CHead d (Bind Abbr) u)) \to (\forall (t: T).((ty3 g d u t) \to (ty3 g c (TLRef n) (lift (S n) O t))))))))
| ty3_abst: \forall (n: nat).(\forall (c: C).(\forall (d: C).(\forall (u: T).((getl n c (CHead d (Bind Abst) u)) \to (\forall (t: T).((ty3 g d u t) \to (ty3 g c (TLRef n) (lift (S n) O u))))))))
| ty3_bind: \forall (c: C).(\forall (u: T).(\forall (t: T).((ty3 g c u t) \to (\forall (b: B).(\forall (t1: T).(\forall (t2: T).((ty3 g (CHead c (Bind b) u) t1 t2) \to (\forall (t0: T).((ty3 g (CHead c (Bind b) u) t2 t0) \to (ty3 g c (THead (Bind b) u t1) (THead (Bind b) u t2)))))))))))
| ty3_appl: \forall (c: C).(\forall (w: T).(\forall (u: T).((ty3 g c w u) \to (\forall (v: T).(\forall (t: T).((ty3 g c v (THead (Bind Abst) u t)) \to (ty3 g c (THead (Flat Appl) w v) (THead (Flat Appl) w (THead (Bind Abst) u t)))))))))
| ty3_cast: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c t1 t2) \to (\forall (t0: T).((ty3 g c t2 t0) \to (ty3 g c (THead (Flat Cast) t2 t1) t2)))))).

axiom ty3_gen_sort: \forall (g: G).(\forall (c: C).(\forall (x: T).(\forall (n: nat).((ty3 g c (TSort n) x) \to (pc3 c (TSort (next g n)) x))))) .

axiom ty3_gen_lref: \forall (g: G).(\forall (c: C).(\forall (x: T).(\forall (n: nat).((ty3 g c (TLRef n) x) \to (or (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 c (lift (S n) O t) x)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(pc3 c (lift (S n) O u) x)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c (CHead e (Bind Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t)))))))))) .

axiom ty3_gen_bind: \forall (g: G).(\forall (b: B).(\forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall (x: T).((ty3 g c (THead (Bind b) u t1) x) \to (ex4_3 T T T (\lambda (t2: T).(\lambda (_: T).(\lambda (_: T).(pc3 c (THead (Bind b) u t2) x)))) (\lambda (_: T).(\lambda (t: T).(\lambda (_: T).(ty3 g c u t)))) (\lambda (t2: T).(\lambda (_: T).(\lambda (_: T).(ty3 g (CHead c (Bind b) u) t1 t2)))) (\lambda (t2: T).(\lambda (_: T).(\lambda (t0: T).(ty3 g (CHead c (Bind b) u) t2 t0))))))))))) .

axiom ty3_gen_appl: \forall (g: G).(\forall (c: C).(\forall (w: T).(\forall (v: T).(\forall (x: T).((ty3 g c (THead (Flat Appl) w v) x) \to (ex3_2 T T (\lambda (u: T).(\lambda (t: T).(pc3 c (THead (Flat Appl) w (THead (Bind Abst) u t)) x))) (\lambda (u: T).(\lambda (t: T).(ty3 g c v (THead (Bind Abst) u t)))) (\lambda (u: T).(\lambda (_: T).(ty3 g c w u))))))))) .

axiom ty3_gen_cast: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).(\forall (x: T).((ty3 g c (THead (Flat Cast) t2 t1) x) \to (land (pc3 c t2 x) (ty3 g c t1 t2))))))) .

axiom ty3_lift: \forall (g: G).(\forall (e: C).(\forall (t1: T).(\forall (t2: T).((ty3 g e t1 t2) \to (\forall (c: C).(\forall (d: nat).(\forall (h: nat).((drop h d c e) \to (ty3 g c (lift h d t1) (lift h d t2)))))))))) .

axiom ty3_correct: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c t1 t2) \to (ex T (\lambda (t: T).(ty3 g c t2 t))))))) .

axiom ty3_unique: \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).((ty3 g c u t1) \to (\forall (t2: T).((ty3 g c u t2) \to (pc3 c t1 t2))))))) .

axiom ty3_fsubst0: \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t: T).((ty3 g c1 t1 t) \to (\forall (i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t2: T).((fsubst0 i u c1 t1 c2 t2) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (ty3 g c2 t2 t)))))))))))) .

axiom ty3_csubst0: \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c1 t1 t2) \to (\forall (e: C).(\forall (u: T).(\forall (i: nat).((getl i c1 (CHead e (Bind Abbr) u)) \to (\forall (c2: C).((csubst0 i u c1 c2) \to (ty3 g c2 t1 t2))))))))))) .

axiom ty3_subst0: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t: T).((ty3 g c t1 t) \to (\forall (e: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead e (Bind Abbr) u)) \to (\forall (t2: T).((subst0 i u t1 t2) \to (ty3 g c t2 t))))))))))) .

axiom ty3_gen_cabbr: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c t1 t2) \to (\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl d c (CHead e (Bind Abbr) u)) \to (\forall (a0: C).((csubst1 d u c a0) \to (\forall (a: C).((drop (S O) d a0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u t1 (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d u t2 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))))))))))))))) .

axiom ty3_gen_cvoid: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c t1 t2) \to (\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl d c (CHead e (Bind Void) u)) \to (\forall (a: C).((drop (S O) d c a) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T t1 (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t2 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))))))))))))) .

inductive csub3 (g:G): C \to (C \to Prop) \def
| csub3_sort: \forall (n: nat).(csub3 g (CSort n) (CSort n))
| csub3_head: \forall (c1: C).(\forall (c2: C).((csub3 g c1 c2) \to (\forall (k: K).(\forall (u: T).(csub3 g (CHead c1 k u) (CHead c2 k u))))))
| csub3_void: \forall (c1: C).(\forall (c2: C).((csub3 g c1 c2) \to (\forall (b: B).((not (eq B b Void)) \to (\forall (u1: T).(\forall (u2: T).(csub3 g (CHead c1 (Bind Void) u1) (CHead c2 (Bind b) u2))))))))
| csub3_abst: \forall (c1: C).(\forall (c2: C).((csub3 g c1 c2) \to (\forall (u: T).(\forall (t: T).((ty3 g c2 u t) \to (csub3 g (CHead c1 (Bind Abst) t) (CHead c2 (Bind Abbr) u))))))).

axiom csub3_gen_abbr: \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v: T).((csub3 g (CHead e1 (Bind Abbr) v) c2) \to (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csub3 g e1 e2))))))) .

axiom csub3_gen_abst: \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v1: T).((csub3 g (CHead e1 (Bind Abst) v1) c2) \to (or (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csub3 g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csub3 g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1))))))))) .

axiom csub3_gen_bind: \forall (g: G).(\forall (b1: B).(\forall (e1: C).(\forall (c2: C).(\forall (v1: T).((csub3 g (CHead e1 (Bind b1) v1) c2) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csub3 g e1 e2)))))))))) .

axiom csub3_refl: \forall (g: G).(\forall (c: C).(csub3 g c c)) .

axiom csub3_clear_conf: \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csub3 g c1 c2) \to (\forall (e1: C).((clear c1 e1) \to (ex2 C (\lambda (e2: C).(csub3 g e1 e2)) (\lambda (e2: C).(clear c2 e2)))))))) .

axiom csub3_drop_flat: \forall (g: G).(\forall (f: F).(\forall (n: nat).(\forall (c1: C).(\forall (c2: C).((csub3 g c1 c2) \to (\forall (d1: C).(\forall (u: T).((drop n O c1 (CHead d1 (Flat f) u)) \to (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(drop n O c2 (CHead d2 (Flat f) u)))))))))))) .

axiom csub3_drop_abbr: \forall (g: G).(\forall (n: nat).(\forall (c1: C).(\forall (c2: C).((csub3 g c1 c2) \to (\forall (d1: C).(\forall (u: T).((drop n O c1 (CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(drop n O c2 (CHead d2 (Bind Abbr) u))))))))))) .

axiom csub3_drop_abst: \forall (g: G).(\forall (n: nat).(\forall (c1: C).(\forall (c2: C).((csub3 g c1 c2) \to (\forall (d1: C).(\forall (t: T).((drop n O c1 (CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(drop n O c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop n O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))))))))))) .

axiom csub3_getl_abbr: \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (u: T).(\forall (n: nat).((getl n c1 (CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).((csub3 g c1 c2) \to (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u))))))))))) .

axiom csub3_getl_abst: \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (t: T).(\forall (n: nat).((getl n c1 (CHead d1 (Bind Abst) t)) \to (\forall (c2: C).((csub3 g c1 c2) \to (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))))))))))) .

axiom csub3_pr2: \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((pr2 c1 t1 t2) \to (\forall (c2: C).((csub3 g c1 c2) \to (pr2 c2 t1 t2))))))) .

axiom csub3_pc3: \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((pc3 c1 t1 t2) \to (\forall (c2: C).((csub3 g c1 c2) \to (pc3 c2 t1 t2))))))) .

axiom csub3_ty3: \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c1 t1 t2) \to (\forall (c2: C).((csub3 g c1 c2) \to (ty3 g c2 t1 t2))))))) .

axiom csub3_ty3_ld: \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (v: T).((ty3 g c u v) \to (\forall (t1: T).(\forall (t2: T).((ty3 g (CHead c (Bind Abst) v) t1 t2) \to (ty3 g (CHead c (Bind Abbr) u) t1 t2)))))))) .

axiom ty3_sred_wcpr0_pr0: \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t: T).((ty3 g c1 t1 t) \to (\forall (c2: C).((wcpr0 c1 c2) \to (\forall (t2: T).((pr0 t1 t2) \to (ty3 g c2 t2 t))))))))) .

axiom ty3_sred_pr1: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr1 t1 t2) \to (\forall (g: G).(\forall (t: T).((ty3 g c t1 t) \to (ty3 g c t2 t))))))) .

axiom ty3_sred_pr2: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (g: G).(\forall (t: T).((ty3 g c t1 t) \to (ty3 g c t2 t))))))) .

axiom ty3_sred_pr3: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall (g: G).(\forall (t: T).((ty3 g c t1 t) \to (ty3 g c t2 t))))))) .

axiom ty3_cred_pr2: \forall (g: G).(\forall (c: C).(\forall (v1: T).(\forall (v2: T).((pr2 c v1 v2) \to (\forall (b: B).(\forall (t1: T).(\forall (t2: T).((ty3 g (CHead c (Bind b) v1) t1 t2) \to (ty3 g (CHead c (Bind b) v2) t1 t2))))))))) .

axiom ty3_cred_pr3: \forall (g: G).(\forall (c: C).(\forall (v1: T).(\forall (v2: T).((pr3 c v1 v2) \to (\forall (b: B).(\forall (t1: T).(\forall (t2: T).((ty3 g (CHead c (Bind b) v1) t1 t2) \to (ty3 g (CHead c (Bind b) v2) t1 t2))))))))) .

axiom ty3_gen__le_S_minus: \forall (d: nat).(\forall (h: nat).(\forall (n: nat).((le (plus d h) n) \to (le d (S (minus n h)))))) .

axiom ty3_gen_lift: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (x: T).(\forall (h: nat).(\forall (d: nat).((ty3 g c (lift h d t1) x) \to (\forall (e: C).((drop h d c e) \to (ex2 T (\lambda (t2: T).(pc3 c (lift h d t2) x)) (\lambda (t2: T).(ty3 g e t1 t2))))))))))) .

axiom ty3_tred: \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).((ty3 g c u t1) \to (\forall (t2: T).((pr3 c t1 t2) \to (ty3 g c u t2))))))) .

axiom ty3_sconv_pc3: \forall (g: G).(\forall (c: C).(\forall (u1: T).(\forall (t1: T).((ty3 g c u1 t1) \to (\forall (u2: T).(\forall (t2: T).((ty3 g c u2 t2) \to ((pc3 c u1 u2) \to (pc3 c t1 t2))))))))) .

axiom ty3_sred_back: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t0: T).((ty3 g c t1 t0) \to (\forall (t2: T).((pr3 c t1 t2) \to (\forall (t: T).((ty3 g c t2 t) \to (ty3 g c t1 t))))))))) .

axiom ty3_sconv: \forall (g: G).(\forall (c: C).(\forall (u1: T).(\forall (t1: T).((ty3 g c u1 t1) \to (\forall (u2: T).(\forall (t2: T).((ty3 g c u2 t2) \to ((pc3 c u1 u2) \to (ty3 g c u1 t2))))))))) .

axiom ty3_tau0: \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).((ty3 g c u t1) \to (\forall (t2: T).((tau0 g c u t2) \to (ty3 g c u t2))))))) .

axiom ty3_arity: \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c t1 t2) \to (ex2 A (\lambda (a1: A).(arity g c t1 a1)) (\lambda (a1: A).(arity g c t2 (asucc g a1)))))))) .

axiom ty3_predicative: \forall (g: G).(\forall (c: C).(\forall (v: T).(\forall (t: T).(\forall (u: T).((ty3 g c (THead (Bind Abst) v t) u) \to ((pc3 c u v) \to (\forall (P: Prop).P))))))) .

axiom ty3_acyclic: \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (u: T).((ty3 g c t u) \to ((pc3 c u t) \to (\forall (P: Prop).P)))))) .

axiom ty3_sn3: \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (u: T).((ty3 g c t u) \to (sn3 c t))))) .

axiom pc3_dec: \forall (g: G).(\forall (c: C).(\forall (u1: T).(\forall (t1: T).((ty3 g c u1 t1) \to (\forall (u2: T).(\forall (t2: T).((ty3 g c u2 t2) \to (or (pc3 c u1 u2) ((pc3 c u1 u2) \to (\forall (P: Prop).P)))))))))) .

axiom pc3_abst_dec: \forall (g: G).(\forall (c: C).(\forall (u1: T).(\forall (t1: T).((ty3 g c u1 t1) \to (\forall (u2: T).(\forall (t2: T).((ty3 g c u2 t2) \to (or (ex4_2 T T (\lambda (u: T).(\lambda (_: T).(pc3 c u1 (THead (Bind Abst) u2 u)))) (\lambda (u: T).(\lambda (v2: T).(ty3 g c (THead (Bind Abst) v2 u) t1))) (\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) (\lambda (_: T).(\lambda (v2: T).(nf2 c v2)))) (\forall (u: T).((pc3 c u1 (THead (Bind Abst) u2 u)) \to (\forall (P: Prop).P))))))))))) .

axiom ty3_inference: \forall (g: G).(\forall (c: C).(\forall (t1: T).(or (ex T (\lambda (t2: T).(ty3 g c t1 t2))) (\forall (t2: T).((ty3 g c t1 t2) \to (\forall (P: Prop).P)))))) .

