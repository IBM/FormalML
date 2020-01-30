open Format

open NnoptExtracted.API
open Util
open Pretty


let () = Format.printf "Result of running opt: %a\n" (pretty_visible_option pretty_df_env) opt ;;
let () = Format.printf "Result of running opt2: %a\n" (pretty_visible_option pretty_df_env) opt2 ;;
let () = Format.printf "The testopt environment: %a\n" pretty_df_env testopt ;;
let () = Format.printf "The testreeopt environment: %a\n" pretty_df_env testreeopt ;;

let () = Format.printf "The gradenv environment: %a\n" pretty_df_env gradenv ;;
let () = Format.printf "The gradenv_tree environment: %a\n" pretty_df_env gradenv_tree ;;

let () = Format.printf "The test_update environment: %a\n" pretty_df_env test_update ;;

let () = Format.printf "The test environment: %a\n" pretty_df_env test_env ;;

let data = read_int_matrix_from_csv "breast-cancer-wisconsin.data" ;;
let actual_data = discard_first data ;;

let () = Format.printf "first part of data without the first column: %d\n" (List.hd (List.hd actual_data))
let normalized_data = normalizeIntData actual_data ;;
let () = Format.printf "first 10 rows of normalized data without the first column: \n%a\n" ( pretty_matrix 10 10) normalized_data ;; 

let () = Random.self_init()

let randomStream = mkIndexedStream 0 (Obj.magic (random_float_vector ())) ;;
let fvals = fst(streamtake 5 randomStream) ;;
let () = Format.printf "random list : %a\n" (pretty_blist pp_print_float) fvals ;;

let init_env = init_env2 9 15 1 (char_list_of_string "w") (char_list_of_string "b") 
    (Obj.magic (random_float_matrix ())) (Obj.magic (random_float_matrix ())) ;;
let () = Format.printf "Init environment: %a\n" pretty_df_env init_env ;;

let wval = eval_wisconsin_batch 500 (Obj.magic init_env) (Obj.magic normalized_data) ;;
let () = Format.printf "wisconsin lost value : %a\n" (pretty_blist pp_print_float) (Obj.magic wval) ;;

let wval2 = wisconsin_test 500 10 (Obj.magic init_env) (Obj.magic normalized_data) ;;
let () = Format.printf "wisconsin lost value : %a\n" (pretty_blist pp_print_float) (Obj.magic wval) ;;








