module EC = RecommCheck
module ES = RecommStep
module ET = RecommTypes

let d_line = ref ES.id

let r_line = ref ES.id

let k_exit k st out ins =
  if st <> ET.OK then k ET.KO out ins else
  k st out ins

let k_for k st outs ins =
  if st <> ET.OK then k ET.KO outs ins else
  match ins with
  | "FOR" :: tl -> !d_line (k_exit k) ET.OO ("FOR" :: outs) tl
  | _           -> k ET.KO outs ins

let k_or k st outs ins =
  if st <> ET.OO then k st outs ins else
  !r_line (k_for k) st outs ins

let step k st outs ins =
  if st = ET.KO then k st outs ins else
  !d_line (k_or k) ET.OO outs ins

let register_d =
  ES.register d_line

let register_r =
  ES.register r_line

let main =
  EC.register_c step
