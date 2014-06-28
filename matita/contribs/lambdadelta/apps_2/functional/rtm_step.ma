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

include "apps_2/functional/rtm.ma".

(* REDUCTION AND TYPE MACHINE ***********************************************)

(* transitions *)
inductive rtm_step: relation rtm ≝
| rtm_drop : ∀G,u,E,I,t,D,V,S,i.
              rtm_step (mk_rtm G u (E. ④{I} {t, D, V}) S (#(i + 1)))
                       (mk_rtm G u E S (#i))
| rtm_ldelta: ∀G,u,E,t,D,V,S.
              rtm_step (mk_rtm G u (E. ④{Abbr} {t, D, V}) S (#0))
                       (mk_rtm G u D S V)
| rtm_ltype : ∀G,u,E,t,D,V,S.
              rtm_step (mk_rtm G u (E. ④{Abst} {t, D, V}) S (#0))
                       (mk_rtm G u D S V)
| rtm_gdrop : ∀G,I,V,u,E,S,p. p < |G| →
              rtm_step (mk_rtm (G. ⓑ{I} V) u E S (§p))
                       (mk_rtm G u E S (§p))
| rtm_gdelta: ∀G,V,u,E,S,p. p = |G| →
              rtm_step (mk_rtm (G. ⓓV) u E S (§p))
                       (mk_rtm G u E S V)
| rtm_gtype : ∀G,V,u,E,S,p. p = |G| →
              rtm_step (mk_rtm (G. ⓛV) u E S (§p))
                       (mk_rtm G u E S V)
| rtm_eps   : ∀G,u,E,S,W,T.
              rtm_step (mk_rtm G u E S (ⓝW. T))
                       (mk_rtm G u E S T)
| rtm_appl  : ∀G,u,E,S,V,T.
              rtm_step (mk_rtm G u E S (ⓐV. T))
                       (mk_rtm G u E ({E, V} @ S) T)
| rtm_beta  : ∀G,u,E,D,V,S,W,T.
              rtm_step (mk_rtm G u E ({D, V} @ S) (+ⓛW. T))
                       (mk_rtm G u (E. ④{Abbr} {u, D, V}) S T)
| rtm_push  : ∀G,u,E,W,T.
              rtm_step (mk_rtm G u E (⟠) (+ⓛW. T))
                       (mk_rtm G (u + 1) (E. ④{Abst} {u, E, W}) (⟠) T)
| rtm_theta : ∀G,u,E,S,V,T.
              rtm_step (mk_rtm G u E S (+ⓓV. T))
                       (mk_rtm G u (E. ④{Abbr} {u, E, V}) S T)
.

interpretation "sequential reduction (RTM)"
   'SRed O1 O2 = (rtm_step O1 O2).
