open Format

open NnoptExtracted.API
open Util
open Pretty


let () = Format.printf "Result of running opt: %a\n" (pretty_visible_option pretty_df_env) opt ;;
let () = Format.printf "The test environment: %a\n" pretty_df_env test_env ;;

let data = read_int_matrix_from_csv "breast-cancer-wisconsin.data" ;;
let () = Format.printf "first part of data: %d" (List.hd (List.hd data))
