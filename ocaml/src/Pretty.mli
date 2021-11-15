open API
open DefinedFunctions
open Vector

val pretty_subVar : Format.formatter -> coq_SubVar -> unit

val pretty_definition_function_types : Format.formatter -> definition_function_types -> unit

val pretty_vector : int -> Format.formatter -> float coq_Vector -> unit
val pretty_matrix : int -> int -> Format.formatter -> float coq_Matrix -> unit

val pretty_var_type : Format.formatter -> var_type -> unit

val pretty_env_entry_type : Format.formatter -> env_entry_type -> unit
val pretty_df_env : Format.formatter -> df_env -> unit

val pretty_visible_option : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit

val pretty_blist : ?bstart:string -> ?bend:string -> ?bsep:string -> (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
