let string_of_char_list l =
  let b = Bytes.create (List.length l) in
  let i = ref 0 in
  List.iter (fun c -> Bytes.set b !i c; incr i) l;
  Bytes.to_string b

let char_list_of_string s =
  let l = ref [] in
  String.iter (fun c -> l := c :: !l) s;
  List.rev !l

let read_int_matrix_from_csv name =
  let sdata = Csv.load name in
  List.map (List.map int_of_string) sdata
