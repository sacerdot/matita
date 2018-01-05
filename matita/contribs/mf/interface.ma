(* (C) 2014 Luca Bressan *)

include "model.ma".

include "pisigma2.ma".
include "power_one.ma".
include "power.ma".

include "pisigma.ma".
include "empty.ma".
include "singleton.ma".
include "list.ma".
include "plus.ma".
include "de.ma".

definition eFalsum: eprop ≝ Falsum.
definition eId: ∀B: ecl. Sup B → Sup B → eprop ≝ Eq.
definition eImplies: eprop → eprop → eprop ≝ Implies.
definition eConj: eprop → eprop → eprop ≝ Conj.
definition eDisj: eprop → eprop → eprop ≝ Disj.

definition efalsum: eprops ≝ falsum.
definition eid: ∀B: est. sup B → sup B → eprops ≝ eq.
definition eimplies: eprops → eprops → eprops ≝ implies.
definition econj: eprops → eprops → eprops ≝ conj.
definition edisj: eprops → eprops → eprops ≝ disj.

