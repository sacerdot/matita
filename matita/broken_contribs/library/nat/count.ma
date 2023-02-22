(**************************************************************************)
(*       __                                                               *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "nat/relevant_equations.ma".
include "nat/sigma_and_pi.ma".
include "nat/permutation.ma".

theorem sigma_f_g : \forall n,m:nat.\forall f,g:nat \to nat.
sigma n (\lambda p.f p + g p) m = sigma n f m + sigma n g m.
intros.elim n.
simplify.reflexivity.
simplify.rewrite > H.
rewrite > assoc_plus.
rewrite < (assoc_plus (g (S (n1+m)))).
rewrite > (sym_plus (g (S (n1+m)))).
rewrite > (assoc_plus (sigma n1 f m)).
rewrite < assoc_plus.
reflexivity.
qed.

theorem sigma_plus: \forall n,p,m:nat.\forall f:nat \to nat.
sigma (S (p+n)) f m = sigma p (\lambda x.(f ((S n) + x))) m + sigma n f m.
intros. elim p.
simplify.
reflexivity.
simplify.
rewrite > assoc_plus in \vdash (? ? ? %).
rewrite < H.
simplify.
rewrite < plus_n_Sm.
rewrite > (sym_plus n).
rewrite > assoc_plus.
rewrite < (sym_plus m).
rewrite < (assoc_plus n1).
reflexivity.
qed.

theorem sigma_plus1: \forall n,p,m:nat.\forall f:nat \to nat.
sigma (p+(S n)) f m = sigma p (\lambda x.(f ((S n) + x))) m + sigma n f m.
intros. elim p.
simplify.reflexivity.
simplify.
rewrite > assoc_plus in \vdash (? ? ? %).
rewrite < H.
rewrite < plus_n_Sm.
rewrite < plus_n_Sm.simplify.
rewrite < (sym_plus n).
rewrite > assoc_plus.
rewrite < (sym_plus m).
rewrite < (assoc_plus n).
reflexivity.
qed.

theorem eq_sigma_sigma : \forall n,m:nat.\forall f:nat \to nat.
sigma (pred ((S n)*(S m))) f O =
sigma m (\lambda a.(sigma n (\lambda b.f (b*(S m) + a)) O)) O.
intro.elim n.simplify.
rewrite < plus_n_O.
apply eq_sigma.intros.reflexivity.
simplify.
rewrite > sigma_f_g.
rewrite < plus_n_O.
rewrite < H.
rewrite > (S_pred ((S n1)*(S m))).
apply sigma_plus1.
simplify.unfold lt.apply le_S_S.apply le_O_n.
qed.

theorem eq_sigma_sigma1 : \forall n,m:nat.\forall f:nat \to nat.
sigma (pred ((S n)*(S m))) f O =
sigma n (\lambda a.(sigma m (\lambda b.f (b*(S n) + a)) O)) O.
intros.
rewrite > sym_times.
apply eq_sigma_sigma.
qed.

theorem sigma_times: \forall n,m,p:nat.\forall f:nat \to nat.
(sigma n f m)*p = sigma n (\lambda i.(f i) * p) m.
intro. elim n.simplify.reflexivity.
simplify.rewrite < H.
apply times_plus_l.
qed.

definition bool_to_nat: bool \to nat \def
\lambda b. match b with
[ true \Rightarrow (S O)
| false \Rightarrow O ].

theorem bool_to_nat_andb: \forall a,b:bool.
bool_to_nat (andb a b) = (bool_to_nat a)*(bool_to_nat b).
intros. elim a.elim b.
simplify.reflexivity.
reflexivity.
reflexivity.
qed.

definition count : nat \to (nat \to bool) \to nat \def
\lambda n.\lambda f. sigma (pred n) (\lambda n.(bool_to_nat (f n))) O.

theorem count_times:\forall n,m:nat. 
\forall f,f1,f2:nat \to bool.
\forall g:nat \to nat \to nat. 
\forall g1,g2: nat \to nat.
(\forall a,b:nat. a < (S n) \to b < (S m) \to (g b a) < (S n)*(S m)) \to
(\forall a,b:nat. a < (S n) \to b < (S m) \to (g1 (g b a)) = a) \to
(\forall a,b:nat. a < (S n) \to b < (S m) \to (g2 (g b a)) = b) \to
(\forall a,b:nat. a < (S n) \to b < (S m) \to f (g b a) = andb (f2 b) (f1 a)) \to
(count ((S n)*(S m)) f) = (count (S n) f1)*(count (S m) f2).
intros.unfold count.
rewrite < eq_map_iter_i_sigma.
rewrite > (permut_to_eq_map_iter_i plus assoc_plus sym_plus ? ? ? 
           (\lambda i.g (div i (S n)) (mod i (S n)))).
rewrite > eq_map_iter_i_sigma.
rewrite > eq_sigma_sigma1.
apply (trans_eq ? ?
(sigma n (\lambda a.
  sigma m (\lambda b.(bool_to_nat (f2 b))*(bool_to_nat (f1 a))) O) O)).
apply eq_sigma.intros.
apply eq_sigma.intros.
rewrite > (div_mod_spec_to_eq (i1*(S n) + i) (S n) ((i1*(S n) + i)/(S n)) 
                                        ((i1*(S n) + i) \mod (S n)) i1 i).
rewrite > (div_mod_spec_to_eq2 (i1*(S n) + i) (S n) ((i1*(S n) + i)/(S n)) 
                                        ((i1*(S n) + i) \mod (S n)) i1 i).
rewrite > H3.
apply bool_to_nat_andb.
unfold lt.apply le_S_S.assumption.
unfold lt.apply le_S_S.assumption.
apply div_mod_spec_div_mod.
unfold lt.apply le_S_S.apply le_O_n.
constructor 1.unfold lt.apply le_S_S.assumption.
reflexivity.
apply div_mod_spec_div_mod.
unfold lt.apply le_S_S.apply le_O_n.
constructor 1.unfold lt.apply le_S_S.assumption.
reflexivity.
apply (trans_eq ? ? 
(sigma n (\lambda n.((bool_to_nat (f1 n)) *
(sigma m (\lambda n.bool_to_nat (f2 n)) O))) O)).
apply eq_sigma.
intros.
rewrite > sym_times.
apply (trans_eq ? ? 
(sigma m (\lambda n.(bool_to_nat (f2 n))*(bool_to_nat (f1 i))) O)).
reflexivity.
apply sym_eq. apply sigma_times.
simplify.
apply sym_eq. apply sigma_times.
unfold permut.
split.
intros.
rewrite < plus_n_O.
apply le_S_S_to_le.
rewrite < S_pred in \vdash (? ? %).
change with ((g (i/(S n)) (i \mod (S n))) \lt (S n)*(S m)).
apply H.
apply lt_mod_m_m.
unfold lt. apply le_S_S.apply le_O_n.
apply (lt_times_to_lt_l n).
apply (le_to_lt_to_lt ? i).
rewrite > (div_mod i (S n)) in \vdash (? ? %).
rewrite > sym_plus.
apply le_plus_n.
unfold lt. apply le_S_S.apply le_O_n.
unfold lt.
rewrite > S_pred in \vdash (? ? %).
apply le_S_S.
rewrite > plus_n_O in \vdash (? ? %).
rewrite > sym_times. assumption.
rewrite > (times_n_O O).
apply lt_times.
unfold lt. apply le_S_S.apply le_O_n.
unfold lt. apply le_S_S.apply le_O_n.
rewrite > (times_n_O O).
apply lt_times.
unfold lt. apply le_S_S.apply le_O_n.
unfold lt. apply le_S_S.apply le_O_n.
rewrite < plus_n_O.
unfold injn.
intros.
cut (i < (S n)*(S m)).
cut (j < (S n)*(S m)).
cut ((i \mod (S n)) < (S n)).
cut ((i/(S n)) < (S m)).
cut ((j \mod (S n)) < (S n)).
cut ((j/(S n)) < (S m)).
rewrite > (div_mod i (S n)).
rewrite > (div_mod j (S n)).
rewrite < (H1 (i \mod (S n)) (i/(S n)) Hcut2 Hcut3).
rewrite < (H2 (i \mod (S n)) (i/(S n)) Hcut2 Hcut3) in \vdash (? ? (? % ?) ?).
rewrite < (H1 (j \mod (S n)) (j/(S n)) Hcut4 Hcut5).
rewrite < (H2 (j \mod (S n)) (j/(S n)) Hcut4 Hcut5) in \vdash (? ? ? (? % ?)).
rewrite > H6.reflexivity.
unfold lt. apply le_S_S.apply le_O_n.
unfold lt. apply le_S_S.apply le_O_n.
apply (lt_times_to_lt_l n).
apply (le_to_lt_to_lt ? j).
rewrite > (div_mod j (S n)) in \vdash (? ? %).
rewrite > sym_plus.
apply le_plus_n.
unfold lt. apply le_S_S.apply le_O_n.
rewrite < sym_times. assumption.
apply lt_mod_m_m.
unfold lt. apply le_S_S.apply le_O_n.
apply (lt_times_to_lt_l n).
apply (le_to_lt_to_lt ? i).
rewrite > (div_mod i (S n)) in \vdash (? ? %).
rewrite > sym_plus.
apply le_plus_n.
unfold lt. apply le_S_S.apply le_O_n.
rewrite < sym_times. assumption.
apply lt_mod_m_m.
unfold lt. apply le_S_S.apply le_O_n.
unfold lt.
rewrite > S_pred in \vdash (? ? %).
apply le_S_S.assumption.
rewrite > (times_n_O O).
apply lt_times.
unfold lt. apply le_S_S.apply le_O_n.
unfold lt. apply le_S_S.apply le_O_n.
unfold lt.
rewrite > S_pred in \vdash (? ? %).
apply le_S_S.assumption.
rewrite > (times_n_O O).
apply lt_times.
unfold lt. apply le_S_S.apply le_O_n.
unfold lt. apply le_S_S.apply le_O_n.
intros.
apply False_ind.
apply (not_le_Sn_O m1 H4).
qed.
