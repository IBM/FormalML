open Format

open NnoptExtracted.API
open Util
open Pretty


let () = Format.printf "Result of running opt: %a\n" (pretty_visible_option pretty_df_env) opt ;;
let () = Format.printf "The test environment: %a\n" pretty_df_env test_env ;;

let data = read_int_matrix_from_csv "breast-cancer-wisconsin.data" ;;
let actual_data = discard_first data ;;
let () = Format.printf "first part of data without the first column: %d" (List.hd (List.hd actual_data))

let () = Random.self_init()
let rm = random_float_matrix ();;
let () = Format.printf "random matrix: %a" (pretty_matrix 8 4) (Obj.magic rm);;
    
