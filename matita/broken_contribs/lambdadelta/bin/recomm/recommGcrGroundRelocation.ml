module T = RecommTypes
module R = RecommPccFor

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "UNIFORMITY" :: "CONDITION" :: tl -> k T.OK ("CONDITION" :: "UNIFORMITY" :: outs) tl
  | "UNIFORM" :: "ELEMENTS" :: tl -> k T.OK ("ELEMENTS" :: "UNIFORM" :: outs) tl
  | "TOTALITY" :: "CONDITION" :: tl -> k T.OK ("CONDITION" :: "TOTALITY" :: outs) tl
  | "RELATIONAL" :: "UNION" :: tl -> k T.OK ("UNION" :: "RELATIONAL" :: outs) tl
  | "RELATIONAL" :: "SUBTRACTION" :: tl -> k T.OK ("SUBTRACTION" :: "RELATIONAL" :: outs) tl
  | "RELATIONAL" :: "INTERSECTION" :: tl -> k T.OK ("INTERSECTION" :: "RELATIONAL" :: outs) tl
  | "RELATIONAL" :: "COMPOSITION" :: tl -> k T.OK ("COMPOSITION" :: "RELATIONAL" :: outs) tl
  | "RELATIONAL" :: "CO-COMPOSITION" :: tl -> k T.OK ("CO-COMPOSITION" :: "RELATIONAL" :: outs) tl
  | "POSITIVE" :: "APPLICATION" :: tl -> k T.OK ("APPLICATION" :: "POSITIVE" :: outs) tl
  | "NON-NEGATIVE" :: "APPLICATION" :: tl -> k T.OK ("APPLICATION" :: "NON-NEGATIVE" :: outs) tl
  | "ITERATED" :: "NEXT" :: tl -> k T.OK ("NEXT" :: "ITERATED" :: outs) tl
  | "ITERATED" :: "PUSH" :: tl -> k T.OK ("PUSH" :: "ITERATED" :: outs) tl
  | "INCLUSION" :: tl -> k T.OK ("INCLUSION" :: outs) tl
  | "IDENTITY" :: "ELEMENT" :: tl -> k T.OK ("ELEMENT" :: "IDENTITY" :: outs) tl
  | "IDENTITY" :: "CONDITION" :: tl -> k T.OK ("CONDITION" :: "IDENTITY" :: outs) tl
  | "FINITE" :: "COLENGTH" :: "CONDITION" :: tl -> k T.OK ("CONDITION" :: "COLENGTH" :: "FINITE" :: outs) tl
  | "FINITE" :: "COLENGTH" :: "ASSIGNMENT" :: tl -> k T.OK ("ASSIGNMENT" :: "COLENGTH" :: "FINITE" :: outs) tl
  | "DIVERGENCE" :: "CONDITION" :: tl -> k T.OK ("CONDITION" :: "DIVERGENCE" :: outs) tl
  | "DISJOINTNESS" :: tl -> k T.OK ("DISJOINTNESS" :: outs) tl
  | "BASIC" :: "ELEMENTS" :: tl -> k T.OK ("ELEMENTS" :: "BASIC" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_r step
