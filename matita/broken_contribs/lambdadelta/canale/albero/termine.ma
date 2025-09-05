(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "canale/albero/nome.ma".
include "canale/notazione/termini.ma".

(* Categoria dei termini ****************************************************)

(* Nota: un termine è una combinazione completa di costrutti elementari *)
(* Nota: metavariabili: T, U, V, W, X, Y, Z senza grazie *)
inductive termine: Type[0] ≝
| NRef: (𝕍) → termine
| NAbs: (𝕍) → termine → termine
| Appl: termine → termine → termine
.

coercion NRef.

interpretation
  "termine (categoria)"
  'CategoriaT = (termine).

interpretation
  "astrazione per nome (termine)"
  'AstrazioneNome x T = (NAbs x T).

interpretation
  "applicazione (termine)"
  'Applicazione T V = (Appl T V).

definition termine_I: termine ≝
𝛌𝗑.𝗑.

interpretation
  "termine I (termine)"
  'TermineI= (termine_I).

definition termine_K: termine ≝
𝛌𝗑.𝛌𝗒.𝗑.

interpretation
  "termine K (termine)"
  'TermineK= (termine_K).

definition termine_Z: termine ≝
𝛌𝗑.𝛌𝗒.𝗒.

interpretation
  "termine Z (termine)"
  'TermineZ= (termine_Z).

definition termine_S: termine ≝
𝛌𝗀.𝛌𝖿.𝛌𝗑. 𝗀❨𝗑❩❨𝖿❨𝗑❩❩.

interpretation
  "termine S (termine)"
  'TermineS= (termine_S).

definition termine_B: termine ≝
𝛌𝗀.𝛌𝖿.𝛌𝗑. 𝗀❨𝖿❨𝗑❩❩.

interpretation
  "termine B (termine)"
  'TermineB= (termine_B).

definition termine_C: termine ≝
𝛌𝗀.𝛌𝖿.𝛌𝗑. 𝗀❨𝗑❩❨𝖿❩.

interpretation
  "termine C (termine)"
  'TermineC= (termine_C).

definition termine_W: termine ≝
𝛌𝖿.𝛌𝗑. 𝖿❨𝗑❩.

interpretation
  "termine W (termine)"
  'TermineW= (termine_W).

definition termine_T: termine ≝
𝛌𝗑.𝛌𝖿. 𝖿❨𝗑❨𝗑❩❨𝖿❩❩.

interpretation
  "termine T (termine)"
  'TermineT= (termine_T).

definition termine_Theta: termine ≝
𝗧❨𝗧❩.

interpretation
  "termine Theta (termine)"
  'TermineTheta = (termine_Theta).
