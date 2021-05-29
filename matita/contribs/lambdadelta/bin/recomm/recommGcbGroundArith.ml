module T = RecommTypes
module R = RecommPcsAnd

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "ylt" :: tl -> k T.OK ("ylt" :: outs) tl
  | "yle" :: tl -> k T.OK ("yle" :: outs) tl
  | "ylminus" :: tl -> k T.OK ("ylminus" :: outs) tl
  | "yminus" :: tl -> k T.OK ("ylminus" :: outs) tl
  | "yplus" :: tl -> k T.OK ("yplus" :: outs) tl
  | "ypred" :: tl -> k T.OK ("ypred" :: outs) tl
  | "ysucc" :: tl -> k T.OK ("ysucc" :: outs) tl
  | "nlt" :: tl -> k T.OK ("nlt" :: outs) tl
  | "nle" :: tl -> k T.OK ("nle" :: outs) tl
  | "nmax" :: tl -> k T.OK ("nmax" :: outs) tl
  | "nminus" :: tl -> k T.OK ("nminus" :: outs) tl
  | "nplus" :: tl -> k T.OK ("nplus" :: outs) tl
  | "nrplus" :: tl -> k T.OK ("nrplus" :: outs) tl
  | "rplus" :: tl -> k T.OK ("nrplus" :: outs) tl
  | "npred" :: tl -> k T.OK ("npred" :: outs) tl
  | "nsucc" :: tl -> k T.OK ("nsucc" :: outs) tl
  | "npsucc" :: tl -> k T.OK ("npsucc" :: outs) tl
  | "ntri" :: tl -> k T.OK ("ntri" :: outs) tl
  | "niter" :: tl -> k T.OK ("niter" :: outs) tl
  | "plt" :: tl -> k T.OK ("plt" :: outs) tl
  | "ple" :: tl -> k T.OK ("ple" :: outs) tl
  | "pplus" :: tl -> k T.OK ("pplus" :: outs) tl
  | "ppred" :: tl -> k T.OK ("ppred" :: outs) tl
  | "psucc" :: tl -> k T.OK ("psucc" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_b step
