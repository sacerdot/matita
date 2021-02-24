module D = RecommGcsAttr

let step k ok outs ins =
  if ok then k ok outs ins else
  match ins with
  | "eliminations" :: tl -> k ok ("eliminations" :: outs) tl
  | "eliminators" :: tl -> k ok ("eliminations" :: outs) tl
  | "destructions" :: tl -> k ok ("destructions" :: outs) tl
  | "forward" :: "properties" :: tl -> k ok ("destructions" :: outs) tl
  | "forward" :: "lemmas" :: tl -> k ok ("destructions" :: outs) tl
  | "inversions" :: tl -> k ok ("inversions" :: outs) tl
  | "inversion" :: "properties" :: tl -> k ok ("inversions" :: outs) tl
  | "inversion" :: "lemmas" :: tl -> k ok ("inversions" :: outs) tl
  | "constructions" :: tl -> k ok ("constructions" :: outs) tl
  | "properties" :: tl -> k ok ("constructions" :: outs) tl
  | _ -> k true outs ins

let main =
  RecommCheck.register_s step
