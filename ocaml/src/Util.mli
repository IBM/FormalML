val string_of_char_list : char list -> string
val char_list_of_string : string -> char list

val read_int_matrix_from_csv : string -> int list list

val memoized_vector : (int -> 'a) -> int -> 'a

val random_float_vector : unit -> int -> float
val random_float_matrix : unit -> int -> int -> float
