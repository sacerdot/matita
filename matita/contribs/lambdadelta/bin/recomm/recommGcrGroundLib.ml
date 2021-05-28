module T = RecommTypes
module R = RecommPccFor

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "CONCATENATION" :: tl -> k T.OK ("CONCATENATION" :: outs) tl
  | "APPEND" :: tl -> k T.OK ("CONCATENATION" :: outs) tl
  | "LENGTH" :: tl -> k T.OK ("LENGTH" :: outs) tl
  | "ITERATED" :: "TAIL" :: tl -> k T.OK ("TAIL" :: "ITERATED" :: outs) tl
  | "TAIL" :: tl -> k T.OK ("TAIL" :: outs) tl
  | "HEAD" :: "AND" :: "TAIL" :: tl -> k T.OK ("TAIL" :: "AND" :: "HEAD" :: outs) tl
  | "NAT-LABELED" :: "REFLEXIVE" :: "AND" :: "TRANSITIVE" :: "CLOSURE" :: tl -> k T.OK ("CLOSURE" :: "TRANSITIVE" :: "AND" :: "REFLEXIVE" :: "NAT-LABELED" :: outs) tl
  | "LABELLED" :: "TRANSITIVE" :: "CLOSURE" :: tl -> k T.OK ("CLOSURE" :: "TRANSITIVE" :: "LABELLED" :: outs) tl
  | "TRANSITIVE" :: "CLOSURE" :: tl -> k T.OK ("CLOSURE" :: "TRANSITIVE" :: outs) tl
  | "EXTENSIONAL" :: "EQUIVALENCE" :: tl -> k T.OK ("EQUIVALENCE" :: "EXTENSIONAL" :: outs) tl
  | "DISJUNCTION" :: tl -> k T.OK ("DISJUNCTION" :: outs) tl
  | "CONJUNCTION" :: tl -> k T.OK ("CONJUNCTION" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_r step
