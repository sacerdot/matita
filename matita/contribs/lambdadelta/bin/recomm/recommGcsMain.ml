module T = RecommTypes
module R = RecommCheck
module D = RecommGcsAttr

let step k st outs ins =
  if st = T.KO then k st outs ins else
  match ins with
  | "iterators" :: tl -> k T.OK ("iterators" :: outs) tl
  | "eliminations" :: tl -> k T.OK ("eliminations" :: outs) tl
  | "eliminators" :: tl -> k T.OK ("eliminations" :: outs) tl
  | "equalities" :: tl -> k T.OK ("equalities" :: outs) tl
  | "destructions" :: tl -> k T.OK ("destructions" :: outs) tl
  | "forward" :: "properties" :: tl -> k T.OK ("destructions" :: outs) tl
  | "forward" :: "lemmas" :: tl -> k T.OK ("destructions" :: outs) tl
  | "inversions" :: tl -> k T.OK ("inversions" :: outs) tl
  | "inversion" :: "properties" :: tl -> k T.OK ("inversions" :: outs) tl
  | "inversion" :: "lemmas" :: tl -> k T.OK ("inversions" :: outs) tl
  | "inversion" :: tl -> k T.OK ("inversions" :: outs) tl
  | "constructions" :: tl -> k T.OK ("constructions" :: outs) tl
  | "properties" :: tl -> k T.OK ("constructions" :: outs) tl
  | _ -> k T.KO outs ins

let main =
  R.register_s step
