module EC = RecommCheck
module ES = RecommStep
module ET = RecommTypes

module D = RecommPcsAnd

let p_line = ref ES.id

let step k st outs ins =
  if st = ET.KO then k st outs ins else
  !p_line k ET.OO outs ins

let register_p =
  ES.register p_line

let main =
  EC.register_s step
