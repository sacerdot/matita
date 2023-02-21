(** Extraction of Matita proofs to Dedukti **)

(** Extract a single object and store it in the corresponding module signature. **)
val extract_obj : NCic.status -> NCic.obj -> unit

(** Register the constraint between two universes. **)
val extract_constraint : NCic.status -> NCic.universe -> NCic.universe -> unit

(** Write all the extracted modules and universes to files.
    Universe constraints can change during the translation, which is why
    we shoul delay the output until all modules have been translated. **)
val output_modules : unit -> unit
