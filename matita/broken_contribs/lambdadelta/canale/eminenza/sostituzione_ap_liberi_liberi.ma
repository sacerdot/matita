(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/eminenza/nomi_ap_liberi_le.ma".
include "canale/eminenza/sostituzione_liberi.ma".
include "canale/eminenza/sostituzione_ap_liberi.ma".

(* Sostituzione *************************************************************)

(* Costruzioni coi nomi liberi alla portata e coi nomi liberi ***************)

lemma liberi_sost_le_integra (x) (V) (T):
      ℱ⦋V/x⦌T ⊆ ❨xϵℱT❩ℱV ∪ (ℱT ⧵ ❴x❵).
#x #V #T
@(subset_le_trans … @ liberi_sost_le …)
@subset_or_le_repl //
qed.

lemma liberi_sost_ge_integra (x) (V) (T):
      ℱV ⧸≬ ℬ[x]T →
      ❨xϵℱT❩ℱV ∪ (ℱT ⧵ ❴x❵) ⊆ ℱ⦋V/x⦌T.
#x #V #T #HI
@subset_le_or_sx //
@(subset_le_trans ????? @ liberi_sost_ge_sx …)
/2 width=1 by ap_liberi_ge_integra/
qed.
