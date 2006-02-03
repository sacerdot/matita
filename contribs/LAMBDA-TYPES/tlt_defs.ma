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

set "baseuri" "cic:/matita/LAMBDA-TYPES/tlt_defs".

include "terms_defs.ma".

definition wadd: (nat \to nat) \to nat \to (nat \to nat) \def 
   \lambda map,w,n.
   match n with [
        O     \Rightarrow w
      | (S m) \Rightarrow (map m)
   ].

let rec weight_map (A:Set) (N:Set) (map:nat \to nat) (t:T A N) on t : nat \def 
   match t with [
        (TSort y k)     \Rightarrow O
      | (TLRef y i)     \Rightarrow (map i)
      | (TWag y z w u) \Rightarrow
         match z with [
              (Bind b) \Rightarrow
                 match b with [
                      Abbr \Rightarrow
                        (S ((weight_map A N map w) + (weight_map A N (wadd map (S (weight_map A N map w))) u)))
                    | Abst \Rightarrow 
                        (S ((weight_map A N map w) + (weight_map A N (wadd map O) u)))
                    | Void \Rightarrow 
                        (S ((weight_map A N map w) + (weight_map A N (wadd map O) u)))
                 ]
            | (Flat a) \Rightarrow
                 (S ((weight_map A N map w) + (weight_map A N map u)))
         ]
      | (TGRef y n)     \Rightarrow O
  ].

definition weight: \forall A,N. T A N \to nat \def 
   \lambda A,N. 
   (weight_map A N (\lambda _.O)).

definition tlt: \forall A,N. T A N \to T A N \to Prop \def 
   \lambda A,N,t1,t2. 
   weight A N t1 < weight A N t2.
