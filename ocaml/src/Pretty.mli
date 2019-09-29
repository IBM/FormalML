open NnoptExtracted

val pretty_subVar : Format.formatter -> subVar -> unit

val pretty_definition_function_types : Format.formatter -> definition_function_types -> unit

val pretty_vector : int -> Format.formatter -> float vector -> unit
val pretty_matrix : int -> int -> Format.formatter -> float matrix -> unit

val pretty_var_type : Format.formatter -> var_type -> unit

val pretty_env_entry_type : Format.formatter -> env_entry_type -> unit
val pretty_df_env : Format.formatter -> df_env -> unit

val pretty_visible_option : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit
