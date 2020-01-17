open Format

open NnoptExtracted

let rec subVar_to_list sv =
  begin match sv with
  | Name s -> (Util.string_of_char_list s, [])
  | Sub (v,i) -> let (s,r) = subVar_to_list v in
                 (s, i::r)
  end

let pretty_const_string s ff _ = pp_print_string ff s

let pretty_blist ?(bstart="[") ?(bend="]") ?(bsep=",") pp ff l =
  pp_print_string ff bstart ;
  (pp_print_list ~pp_sep:(pretty_const_string bsep)) pp ff l ;
  pp_print_string ff bend

let pretty_subVar ff sv =
  let (s,l) = subVar_to_list sv in
  pp_print_string ff s ;
  if l <> []
  then pretty_blist pp_print_int ff l

let pretty_definition_function_types ff dft =
  begin match dft with
  | DTfloat -> fprintf ff "%s" "float"
  | DTVector m -> fprintf ff "%s[%d]" "float" m
  | DTMatrix (m,n) -> fprintf ff "%s[%d,%d]" "float" m n
  end

let pretty_var_type ff (sv, dft) =
  fprintf ff "%a{%a}" pretty_subVar sv pretty_definition_function_types dft

let pretty_vector n ff v =
  let fs = List.init n (fun i -> Obj.magic (v i)) in
  pretty_blist pp_print_float ff fs

let pretty_matrix m n ff v =
  let fs = List.init m (fun i -> List.init n (fun j -> Obj.magic (v i j))) in
  pretty_blist (pretty_blist pp_print_float) ff fs

let pretty_definition_function_types_interp ff dft value =
  begin match dft with
  | DTfloat -> pp_print_float ff (Obj.magic value)
  | DTVector m -> pretty_vector m ff (Obj.magic value)
  | DTMatrix (m,n) -> pretty_matrix m n ff (Obj.magic value)
  end

let pretty_env_entry_type ff (ExistT ((sv, dft), value)) =
  pretty_subVar ff sv ;
  pp_print_string ff "->" ;
  pretty_definition_function_types_interp ff dft value

let pretty_df_env ff env =
  pretty_blist ~bstart:"{" ~bend:"}" pretty_env_entry_type ff env

(* This should be replaced with Format.pp_print_option from ocaml >=4.08 *)
let pretty_option ?none some formatter value =
  begin match value with
  | None ->
     begin
       match none with
       | None -> ()
       | Some none -> none formatter ()
     end
  | Some value -> some formatter value
  end

let pretty_visible_option some formatter value = pretty_option ~none:(pretty_const_string "None") some formatter value
