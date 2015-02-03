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

include "ground_1/blt/defs.ma".

theorem lt_blt:
 \forall (x: nat).(\forall (y: nat).((lt y x) \to (eq bool (blt y x) true)))
\def
 \lambda (x: nat).(let TMP_793 \def (\lambda (n: nat).(\forall (y: nat).((lt 
y n) \to (let TMP_792 \def (blt y n) in (eq bool TMP_792 true))))) in (let 
TMP_791 \def (\lambda (y: nat).(\lambda (H: (lt y O)).(let H0 \def (match H 
in le with [le_n \Rightarrow (\lambda (H0: (eq nat (S y) O)).(let TMP_787 
\def (S y) in (let TMP_786 \def (\lambda (e: nat).(match e in nat with [O 
\Rightarrow False | (S _) \Rightarrow True])) in (let H1 \def (eq_ind nat 
TMP_787 TMP_786 I O H0) in (let TMP_788 \def (blt y O) in (let TMP_789 \def 
(eq bool TMP_788 true) in (False_ind TMP_789 H1))))))) | (le_S m H0) 
\Rightarrow (\lambda (H1: (eq nat (S m) O)).(let TMP_782 \def (S m) in (let 
TMP_781 \def (\lambda (e: nat).(match e in nat with [O \Rightarrow False | (S 
_) \Rightarrow True])) in (let H2 \def (eq_ind nat TMP_782 TMP_781 I O H1) in 
(let TMP_784 \def ((le (S y) m) \to (let TMP_783 \def (blt y O) in (eq bool 
TMP_783 true))) in (let TMP_785 \def (False_ind TMP_784 H2) in (TMP_785 
H0)))))))]) in (let TMP_790 \def (refl_equal nat O) in (H0 TMP_790))))) in 
(let TMP_780 \def (\lambda (n: nat).(\lambda (H: ((\forall (y: nat).((lt y n) 
\to (eq bool (blt y n) true))))).(\lambda (y: nat).(let TMP_779 \def (\lambda 
(n0: nat).((lt n0 (S n)) \to (let TMP_777 \def (S n) in (let TMP_778 \def 
(blt n0 TMP_777) in (eq bool TMP_778 true))))) in (let TMP_776 \def (\lambda 
(_: (lt O (S n))).(refl_equal bool true)) in (let TMP_775 \def (\lambda (n0: 
nat).(\lambda (_: (((lt n0 (S n)) \to (eq bool (match n0 with [O \Rightarrow 
true | (S m) \Rightarrow (blt m n)]) true)))).(\lambda (H1: (lt (S n0) (S 
n))).(let TMP_773 \def (S n0) in (let TMP_774 \def (le_S_n TMP_773 n H1) in 
(H n0 TMP_774)))))) in (nat_ind TMP_779 TMP_776 TMP_775 y))))))) in (nat_ind 
TMP_793 TMP_791 TMP_780 x)))).

theorem le_bge:
 \forall (x: nat).(\forall (y: nat).((le x y) \to (eq bool (blt y x) false)))
\def
 \lambda (x: nat).(let TMP_815 \def (\lambda (n: nat).(\forall (y: nat).((le 
n y) \to (let TMP_814 \def (blt y n) in (eq bool TMP_814 false))))) in (let 
TMP_813 \def (\lambda (y: nat).(\lambda (_: (le O y)).(refl_equal bool 
false))) in (let TMP_812 \def (\lambda (n: nat).(\lambda (H: ((\forall (y: 
nat).((le n y) \to (eq bool (blt y n) false))))).(\lambda (y: nat).(let 
TMP_811 \def (\lambda (n0: nat).((le (S n) n0) \to (let TMP_809 \def (S n) in 
(let TMP_810 \def (blt n0 TMP_809) in (eq bool TMP_810 false))))) in (let 
TMP_808 \def (\lambda (H0: (le (S n) O)).(let H1 \def (match H0 in le with 
[le_n \Rightarrow (\lambda (H1: (eq nat (S n) O)).(let TMP_803 \def (S n) in 
(let TMP_802 \def (\lambda (e: nat).(match e in nat with [O \Rightarrow False 
| (S _) \Rightarrow True])) in (let H2 \def (eq_ind nat TMP_803 TMP_802 I O 
H1) in (let TMP_804 \def (S n) in (let TMP_805 \def (blt O TMP_804) in (let 
TMP_806 \def (eq bool TMP_805 false) in (False_ind TMP_806 H2)))))))) | (le_S 
m H1) \Rightarrow (\lambda (H2: (eq nat (S m) O)).(let TMP_797 \def (S m) in 
(let TMP_796 \def (\lambda (e: nat).(match e in nat with [O \Rightarrow False 
| (S _) \Rightarrow True])) in (let H3 \def (eq_ind nat TMP_797 TMP_796 I O 
H2) in (let TMP_800 \def ((le (S n) m) \to (let TMP_798 \def (S n) in (let 
TMP_799 \def (blt O TMP_798) in (eq bool TMP_799 false)))) in (let TMP_801 
\def (False_ind TMP_800 H3) in (TMP_801 H1)))))))]) in (let TMP_807 \def 
(refl_equal nat O) in (H1 TMP_807)))) in (let TMP_795 \def (\lambda (n0: 
nat).(\lambda (_: (((le (S n) n0) \to (eq bool (blt n0 (S n)) 
false)))).(\lambda (H1: (le (S n) (S n0))).(let TMP_794 \def (le_S_n n n0 H1) 
in (H n0 TMP_794))))) in (nat_ind TMP_811 TMP_808 TMP_795 y))))))) in 
(nat_ind TMP_815 TMP_813 TMP_812 x)))).

theorem blt_lt:
 \forall (x: nat).(\forall (y: nat).((eq bool (blt y x) true) \to (lt y x)))
\def
 \lambda (x: nat).(let TMP_834 \def (\lambda (n: nat).(\forall (y: nat).((eq 
bool (blt y n) true) \to (lt y n)))) in (let TMP_833 \def (\lambda (y: 
nat).(\lambda (H: (eq bool (blt y O) true)).(let H0 \def (match H in eq with 
[refl_equal \Rightarrow (\lambda (H0: (eq bool (blt y O) true)).(let TMP_830 
\def (blt y O) in (let TMP_829 \def (\lambda (e: bool).(match e in bool with 
[true \Rightarrow False | false \Rightarrow True])) in (let H1 \def (eq_ind 
bool TMP_830 TMP_829 I true H0) in (let TMP_831 \def (lt y O) in (False_ind 
TMP_831 H1))))))]) in (let TMP_832 \def (refl_equal bool true) in (H0 
TMP_832))))) in (let TMP_828 \def (\lambda (n: nat).(\lambda (H: ((\forall 
(y: nat).((eq bool (blt y n) true) \to (lt y n))))).(\lambda (y: nat).(let 
TMP_827 \def (\lambda (n0: nat).((eq bool (blt n0 (S n)) true) \to (let 
TMP_826 \def (S n) in (lt n0 TMP_826)))) in (let TMP_825 \def (\lambda (_: 
(eq bool true true)).(let TMP_824 \def (S O) in (let TMP_823 \def (S n) in 
(let TMP_821 \def (S O) in (let TMP_820 \def (S n) in (let TMP_818 \def 
(le_O_n n) in (let TMP_819 \def (le_n_S O n TMP_818) in (let TMP_822 \def 
(le_n_S TMP_821 TMP_820 TMP_819) in (le_S_n TMP_824 TMP_823 TMP_822))))))))) 
in (let TMP_817 \def (\lambda (n0: nat).(\lambda (_: (((eq bool (match n0 
with [O \Rightarrow true | (S m) \Rightarrow (blt m n)]) true) \to (lt n0 (S 
n))))).(\lambda (H1: (eq bool (blt n0 n) true)).(let TMP_816 \def (H n0 H1) 
in (lt_n_S n0 n TMP_816))))) in (nat_ind TMP_827 TMP_825 TMP_817 y))))))) in 
(nat_ind TMP_834 TMP_833 TMP_828 x)))).

theorem bge_le:
 \forall (x: nat).(\forall (y: nat).((eq bool (blt y x) false) \to (le x y)))
\def
 \lambda (x: nat).(let TMP_854 \def (\lambda (n: nat).(\forall (y: nat).((eq 
bool (blt y n) false) \to (le n y)))) in (let TMP_853 \def (\lambda (y: 
nat).(\lambda (_: (eq bool (blt y O) false)).(le_O_n y))) in (let TMP_852 
\def (\lambda (n: nat).(\lambda (H: ((\forall (y: nat).((eq bool (blt y n) 
false) \to (le n y))))).(\lambda (y: nat).(let TMP_851 \def (\lambda (n0: 
nat).((eq bool (blt n0 (S n)) false) \to (let TMP_850 \def (S n) in (le 
TMP_850 n0)))) in (let TMP_849 \def (\lambda (H0: (eq bool (blt O (S n)) 
false)).(let H1 \def (match H0 in eq with [refl_equal \Rightarrow (\lambda 
(H1: (eq bool (blt O (S n)) false)).(let TMP_844 \def (S n) in (let TMP_845 
\def (blt O TMP_844) in (let TMP_843 \def (\lambda (e: bool).(match e in bool 
with [true \Rightarrow True | false \Rightarrow False])) in (let H2 \def 
(eq_ind bool TMP_845 TMP_843 I false H1) in (let TMP_846 \def (S n) in (let 
TMP_847 \def (le TMP_846 O) in (False_ind TMP_847 H2))))))))]) in (let 
TMP_848 \def (refl_equal bool false) in (H1 TMP_848)))) in (let TMP_842 \def 
(\lambda (n0: nat).(\lambda (_: (((eq bool (blt n0 (S n)) false) \to (le (S 
n) n0)))).(\lambda (H1: (eq bool (blt (S n0) (S n)) false)).(let TMP_841 \def 
(S n) in (let TMP_840 \def (S n0) in (let TMP_838 \def (S n) in (let TMP_837 
\def (S n0) in (let TMP_835 \def (H n0 H1) in (let TMP_836 \def (le_n_S n n0 
TMP_835) in (let TMP_839 \def (le_n_S TMP_838 TMP_837 TMP_836) in (le_S_n 
TMP_841 TMP_840 TMP_839))))))))))) in (nat_ind TMP_851 TMP_849 TMP_842 
y))))))) in (nat_ind TMP_854 TMP_853 TMP_852 x)))).

