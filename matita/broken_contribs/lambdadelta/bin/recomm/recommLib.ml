let split_on_char c s =
  List.filter ((<>) "") (String.split_on_char c s)
