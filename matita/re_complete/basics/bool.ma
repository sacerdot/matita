include "basics/relations.ma".

(********** bool **********)
inductive bool: Type[0] ≝ 
  | true : bool
  | false : bool.

theorem not_eq_true_false : true ≠ false.
@nmk #Heq destruct
qed.

definition notb : bool → bool ≝
λ b:bool. match b with [true ⇒ false|false ⇒ true ].

interpretation "boolean not" 'not x = (notb x).

theorem notb_elim: ∀ b:bool.∀ P:bool → Prop.
match b with
[ true ⇒ P false
| false ⇒ P true] → P (notb b).
#b #P elim b normalize // qed.

theorem notb_notb: ∀b:bool. notb (notb b) = b.
#b elim b // qed.

theorem injective_notb: injective bool bool notb.
#b1 #b2 #H <(notb_notb b1) <(notb_notb b2) @eq_f // qed.

theorem noteq_to_eqnot: ∀b1,b2. b1 ≠ b2 → b1 = notb b2.
* * // #H @False_ind /2/
qed.

theorem eqnot_to_noteq: ∀b1,b2. b1 = notb b2 → b1 ≠ b2.
* * normalize // #H @(not_to_not … not_eq_true_false) //
qed.

definition andb : bool → bool → bool ≝
λb1,b2:bool. match b1 with [ true ⇒ b2 | false ⇒ false ].

interpretation "boolean and" 'and x y = (andb x y).

theorem andb_elim: ∀ b1,b2:bool. ∀ P:bool → Prop.
match b1 with [ true ⇒ P b2 | false ⇒ P false] → P (b1 ∧ b2).
#b1 #b2 #P (elim b1) normalize // qed.

theorem andb_true_l: ∀ b1,b2. (b1 ∧ b2) = true → b1 = true.
#b1 (cases b1) normalize // qed.

theorem andb_true_r: ∀b1,b2. (b1 ∧ b2) = true → b2 = true.
#b1 #b2 (cases b1) normalize // (cases b2) // qed.

theorem andb_true: ∀b1,b2. (b1 ∧ b2) = true → b1 = true ∧ b2 = true.
/3/ qed.

definition orb : bool → bool → bool ≝
λb1,b2:bool.match b1 with [ true ⇒ true | false ⇒ b2].
 
interpretation "boolean or" 'or x y = (orb x y).

theorem orb_elim: ∀ b1,b2:bool. ∀ P:bool → Prop.
match b1 with [ true ⇒ P true | false ⇒ P b2] → P (orb b1 b2).
#b1 #b2 #P (elim b1) normalize // qed.

lemma orb_true_r1: ∀b1,b2:bool. 
  b1 = true → (b1 ∨ b2) = true.
#b1 #b2 #H >H // qed.

lemma orb_true_r2: ∀b1,b2:bool. 
  b2 = true → (b1 ∨ b2) = true.
#b1 #b2 #H >H cases b1 // qed.

lemma orb_true_l: ∀b1,b2:bool. 
  (b1 ∨ b2) = true → (b1 = true) ∨ (b2 = true).
* normalize /2/ qed.

definition xorb : bool → bool → bool ≝
λb1,b2:bool.
 match b1 with
  [ true ⇒  match b2 with [ true ⇒ false | false ⇒ true ]
  | false ⇒  match b2 with [ true ⇒ true | false ⇒ false ]].

notation > "'if' term 46 e 'then' term 46 t 'else' term 46 f" non associative with precedence 46
 for @{ match $e in bool with [ true ⇒ $t | false ⇒ $f]  }.
notation < "hvbox('if' \nbsp term 46 e \nbsp break 'then' \nbsp term 46 t \nbsp break 'else' \nbsp term 49 f \nbsp)" non associative with precedence 46
 for @{ match $e with [ true ⇒ $t | false ⇒ $f]  }.

theorem bool_to_decidable_eq: 
  ∀b1,b2:bool. decidable (b1=b2).
#b1 #b2 (cases b1) (cases b2) /2/ %2 /3/ qed.

theorem true_or_false:
∀b:bool. b = true ∨ b = false.
#b (cases b) /2/ qed.


