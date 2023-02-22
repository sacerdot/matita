module T = RecommTypes
module R = RecommPcsAnd

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "pr_sor" :: tl -> k T.OK ("pr_sor" :: outs) tl
  | "sor" :: tl -> k T.OK ("pr_sor" :: outs) tl
  | "pr_sand" :: tl -> k T.OK ("pr_sand" :: outs) tl
  | "sand" :: tl -> k T.OK ("pr_sand" :: outs) tl
  | "pr_sdj" :: tl -> k T.OK ("pr_sdj" :: outs) tl
  | "sdj" :: tl -> k T.OK ("pr_sdj" :: outs) tl
  | "pr_sle" :: tl -> k T.OK ("pr_sle" :: outs) tl
  | "sle" :: tl -> k T.OK ("pr_sle" :: outs) tl
  | "inclusion" :: tl -> k T.OK ("pr_sle" :: outs) tl
  | "pr_coafter" :: tl -> k T.OK ("pr_coafter" :: outs) tl
  | "coafter" :: tl -> k T.OK ("pr_coafter" :: outs) tl
  | "pr_after" :: tl -> k T.OK ("pr_after" :: outs) tl
  | "after" :: tl -> k T.OK ("pr_after" :: outs) tl
  | "pr_isd" :: tl -> k T.OK ("pr_isd" :: outs) tl
  | "isdiv" :: tl -> k T.OK ("pr_isd" :: outs) tl
  | "pr_ist" :: tl -> k T.OK ("pr_ist" :: outs) tl
  | "ist" :: tl -> k T.OK ("pr_ist" :: outs) tl
  | "istot" :: tl -> k T.OK ("pr_ist" :: outs) tl
  | "pr_isf" :: tl -> k T.OK ("pr_isf" :: outs) tl
  | "isf" :: tl -> k T.OK ("pr_isf" :: outs) tl
  | "isfin" :: tl -> k T.OK ("pr_isf" :: outs) tl
  | "test" :: "for" :: "finite" :: "colength" :: tl -> k T.OK ("pr_isf" :: outs) tl
  | "pr_fcla" :: tl -> k T.OK ("pr_fcla" :: outs) tl
  | "fcla" :: tl -> k T.OK ("pr_fcla" :: outs) tl
  | "finite" :: "colength" :: "assignment" :: tl -> k T.OK ("pr_fcla" :: outs) tl
  | "finite" :: "colength" :: tl -> k T.OK ("pr_fcla" :: outs) tl
  | "pr_isu" :: tl -> k T.OK ("pr_isu" :: outs) tl
  | "isuni" :: tl -> k T.OK ("pr_isu" :: outs) tl
  | "test" :: "for" :: "uniform" :: "relocations" :: tl -> k T.OK ("pr_isu" :: outs) tl
  | "pr_isi" :: tl -> k T.OK ("pr_isi" :: outs) tl
  | "isi" :: tl -> k T.OK ("pr_isi" :: outs) tl
  | "isid" :: tl -> k T.OK ("pr_isi" :: outs) tl
  | "test" :: "for" :: "identity" :: tl -> k T.OK ("pr_isi" :: outs) tl
  | "pr_nat" :: tl -> k T.OK ("pr_nat" :: outs) tl
  | "nat" :: tl -> k T.OK ("pr_nat" :: outs) tl
  | "pr_pat" :: tl -> k T.OK ("pr_pat" :: outs) tl
  | "pat" :: tl -> k T.OK ("pr_pat" :: outs) tl
  | "at" :: tl -> k T.OK ("pr_pat" :: outs) tl
  | "pr_basic" :: tl -> k T.OK ("pr_basic" :: outs) tl
  | "basic" :: "relocation" :: tl -> k T.OK ("pr_basic" :: outs) tl
  | "pr_uni" :: tl -> k T.OK ("pr_uni" :: outs) tl
  | "uni" :: tl -> k T.OK ("pr_uni" :: outs) tl
  | "uniform" :: "relocations" :: tl -> k T.OK ("pr_uni" :: outs) tl
  | "pr_id" :: tl -> k T.OK ("pr_id" :: outs) tl
  | "id" :: tl -> k T.OK ("pr_id" :: outs) tl
  | "pr_tls" :: tl -> k T.OK ("pr_tls" :: outs) tl
  | "tls" :: tl -> k T.OK ("pr_tls" :: outs) tl
  | "iterated" :: "tail" :: tl -> k T.OK ("pr_tls" :: outs) tl
  | "pr_nexts" :: tl -> k T.OK ("pr_nexts" :: outs) tl
  | "nexts" :: tl -> k T.OK ("pr_nexts" :: outs) tl
  | "iterated" :: "next" :: tl -> k T.OK ("pr_nexts" :: outs) tl
  | "pr_pushs" :: tl -> k T.OK ("pr_pushs" :: outs) tl
  | "pushs" :: tl -> k T.OK ("pr_pushs" :: outs) tl
  | "iterated" :: "push" :: tl -> k T.OK ("pr_pushs" :: outs) tl
  | "pr_tl" :: tl -> k T.OK ("pr_tl" :: outs) tl
  | "tl" :: tl -> k T.OK ("pr_tl" :: outs) tl
  | "tail" :: tl -> k T.OK ("pr_tl" :: outs) tl
  | "pr_eq" :: tl -> k T.OK ("pr_eq" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_b step
