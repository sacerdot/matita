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

set "baseuri" "cic:/matita/Fsub/util".
include "logic/equality.ma".
include "nat/compare.ma".
include "list/list.ma".
include "list/in.ma".

(*** useful definitions and lemmas not really related to Fsub ***)

definition max \def 
\lambda m,n.
  match (leb m n) with
     [true \Rightarrow n
     |false \Rightarrow m]. 
     
lemma le_n_max_m_n: \forall m,n:nat. n \le max m n.
intros.
unfold max.
apply (leb_elim m n)
  [simplify.intros.apply le_n
  |simplify.intros.autobatch
  ]
qed.
  
lemma le_m_max_m_n: \forall m,n:nat. m \le max m n.
intros.
unfold max.
apply (leb_elim m n)
  [simplify.intro.assumption
  |simplify.intros.autobatch
  ]
qed.  

notation > "hvbox(x ∈ l)"
  non associative with precedence 30 for @{ 'inlist $x $l }.
notation < "hvbox(x \nbsp ∈ \nbsp l)"
  non associative with precedence 30 for @{ 'inlist $x $l }.
interpretation "item in list" 'inlist x l =
  (cic:/matita/list/in/in_list.ind#xpointer(1/1) _ x l).

lemma max_case : \forall m,n.(max m n) = match (leb m n) with
      [ true \Rightarrow n
      | false \Rightarrow m ].
intros;elim m;simplify;reflexivity;
qed.