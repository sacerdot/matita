let initialized = ref false

let init () =
 if not !initialized then begin
  initialized := true;
  ignore (GMain.Main.init ())
 end else
  assert false
