module T = RecommTypes
module R = RecommPcsAnd

let step k st outs ins =
  if st <> T.OO then k st outs ins else
  match ins with
  | "gr_sor" :: tl -> k T.OK ("gr_sor" :: outs) tl
  | "sor" :: tl -> k T.OK ("gr_sor" :: outs) tl
  | "gr_sand" :: tl -> k T.OK ("gr_sand" :: outs) tl
  | "sand" :: tl -> k T.OK ("gr_sand" :: outs) tl
  | "gr_sdj" :: tl -> k T.OK ("gr_sdj" :: outs) tl
  | "sdj" :: tl -> k T.OK ("gr_sdj" :: outs) tl
  | "gr_sle" :: tl -> k T.OK ("gr_sle" :: outs) tl
  | "sle" :: tl -> k T.OK ("gr_sle" :: outs) tl
  | "inclusion" :: tl -> k T.OK ("gr_sle" :: outs) tl
  | "gr_coafter" :: tl -> k T.OK ("gr_coafter" :: outs) tl
  | "coafter" :: tl -> k T.OK ("gr_coafter" :: outs) tl
  | "gr_after" :: tl -> k T.OK ("gr_after" :: outs) tl
  | "after" :: tl -> k T.OK ("gr_after" :: outs) tl
  | "gr_isd" :: tl -> k T.OK ("gr_isd" :: outs) tl
  | "isdiv" :: tl -> k T.OK ("gr_isd" :: outs) tl
  | "gr_ist" :: tl -> k T.OK ("gr_ist" :: outs) tl
  | "ist" :: tl -> k T.OK ("gr_ist" :: outs) tl
  | "istot" :: tl -> k T.OK ("gr_ist" :: outs) tl
  | "gr_isf" :: tl -> k T.OK ("gr_isf" :: outs) tl
  | "isf" :: tl -> k T.OK ("gr_isf" :: outs) tl
  | "isfin" :: tl -> k T.OK ("gr_isf" :: outs) tl
  | "test" :: "for" :: "finite" :: "colength" :: tl -> k T.OK ("gr_isf" :: outs) tl
  | "gr_fcla" :: tl -> k T.OK ("gr_fcla" :: outs) tl
  | "fcla" :: tl -> k T.OK ("gr_fcla" :: outs) tl
  | "finite" :: "colength" :: "assignment" :: tl -> k T.OK ("gr_fcla" :: outs) tl
  | "finite" :: "colength" :: tl -> k T.OK ("gr_fcla" :: outs) tl
  | "gr_isu" :: tl -> k T.OK ("gr_isu" :: outs) tl
  | "isuni" :: tl -> k T.OK ("gr_isu" :: outs) tl
  | "test" :: "for" :: "uniform" :: "relocations" :: tl -> k T.OK ("gr_isu" :: outs) tl
  | "gr_isi" :: tl -> k T.OK ("gr_isi" :: outs) tl
  | "isi" :: tl -> k T.OK ("gr_isi" :: outs) tl
  | "isid" :: tl -> k T.OK ("gr_isi" :: outs) tl
  | "test" :: "for" :: "identity" :: tl -> k T.OK ("gr_isi" :: outs) tl
  | "gr_nat" :: tl -> k T.OK ("gr_nat" :: outs) tl
  | "nat" :: tl -> k T.OK ("gr_nat" :: outs) tl
  | "gr_pat" :: tl -> k T.OK ("gr_pat" :: outs) tl
  | "pat" :: tl -> k T.OK ("gr_pat" :: outs) tl
  | "at" :: tl -> k T.OK ("gr_pat" :: outs) tl
  | "gr_basic" :: tl -> k T.OK ("gr_basic" :: outs) tl
  | "basic" :: "relocation" :: tl -> k T.OK ("gr_basic" :: outs) tl
  | "gr_uni" :: tl -> k T.OK ("gr_uni" :: outs) tl
  | "uni" :: tl -> k T.OK ("gr_uni" :: outs) tl
  | "uniform" :: "relocations" :: tl -> k T.OK ("gr_uni" :: outs) tl
  | "gr_id" :: tl -> k T.OK ("gr_id" :: outs) tl
  | "id" :: tl -> k T.OK ("gr_id" :: outs) tl
  | "gr_tls" :: tl -> k T.OK ("gr_tls" :: outs) tl
  | "tls" :: tl -> k T.OK ("gr_tls" :: outs) tl
  | "iterated" :: "tail" :: tl -> k T.OK ("gr_tls" :: outs) tl
  | "gr_nexts" :: tl -> k T.OK ("gr_nexts" :: outs) tl
  | "nexts" :: tl -> k T.OK ("gr_nexts" :: outs) tl
  | "iterated" :: "next" :: tl -> k T.OK ("gr_nexts" :: outs) tl
  | "gr_pushs" :: tl -> k T.OK ("gr_pushs" :: outs) tl
  | "pushs" :: tl -> k T.OK ("gr_pushs" :: outs) tl
  | "iterated" :: "push" :: tl -> k T.OK ("gr_pushs" :: outs) tl
  | "gr_tl" :: tl -> k T.OK ("gr_tl" :: outs) tl
  | "tl" :: tl -> k T.OK ("gr_tl" :: outs) tl
  | "tail" :: tl -> k T.OK ("gr_tl" :: outs) tl
  | "gr_eq" :: tl -> k T.OK ("gr_eq" :: outs) tl
  | _ -> k T.OO outs ins

let main =
  R.register_b step
