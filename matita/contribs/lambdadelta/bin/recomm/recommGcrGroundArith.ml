module T = RecommTypes
module R = RecommPccFor

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "ARITHMETICAL" :: "PROPERTIES" :: tl -> k T.OK ("PROPERTIES" :: "ARITHMETICAL" :: outs) tl
  | "STRICT" :: "ORDER" :: tl -> k T.OK ("ORDER" :: "STRICT" :: outs) tl
  | "ORDER" :: tl -> k T.OK ("ORDER" :: outs) tl
  | "MAXIMUM" :: tl -> k T.OK ("MAXIMUM" :: outs) tl
  | "MAXIMUN" :: tl -> k T.OK ("MAXIMUM" :: outs) tl
  | "LEFT" :: "SUBTRACTION" :: tl -> k T.OK ("SUBTRACTION" :: "LEFT" :: outs) tl
  | "SUBTRACTION" :: tl -> k T.OK ("SUBTRACTION" :: outs) tl
  | "ADDITION" :: tl -> k T.OK ("ADDITION" :: outs) tl
  | "PREDECESSOR" :: tl -> k T.OK ("PREDECESSOR" :: outs) tl
  | "SUCCESSOR" :: tl -> k T.OK ("SUCCESSOR" :: outs) tl
  | "NAT-INJECTION" :: tl -> k T.OK ("NAT-INJECTION" :: outs) tl
  | "TRICHOTOMY" :: "OPERATOR" :: tl -> k T.OK ("OPERATOR" :: "TRICHOTOMY" :: outs) tl
  | "ITERATED" :: "FUNCTION" :: tl -> k T.OK ("FUNCTION" :: "ITERATED" :: outs) tl
  | "DISCRIMINATOR" :: tl -> k T.OK ("DISCRIMINATOR" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_r step
