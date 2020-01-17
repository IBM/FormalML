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

let rec memoized_vector f = 
  let cache = Hashtbl.create 10 in
  begin fun n ->
    try Hashtbl.find cache n
    with Not_found -> begin
        let x = f n in
        Hashtbl.add cache n x; x
    end
  end

let random_float_vector () = memoized_vector (fun _ -> Random.float 1.0)
let random_float_matrix () = memoized_vector (fun _ -> random_float_vector ())

