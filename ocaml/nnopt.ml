open Format

open API
open Util
open Pretty


let () = Format.printf "Result of running opt: %a\n" (pretty_visible_option pretty_df_env) API.opt ;;
let () = Format.printf "Result of running opt2: %a\n" (pretty_visible_option pretty_df_env) API.opt2 ;;
let () = Format.printf "The testopt environment: %a\n" pretty_df_env API.testopt ;;
let () = Format.printf "The testreeopt environment: %a\n" pretty_df_env API.testreeopt ;;

let () = Format.printf "The gradenv environment: %a\n" pretty_df_env API.gradenv ;;
let () = Format.printf "The gradenv_tree environment: %a\n" pretty_df_env API.gradenv_tree ;;

let () = Format.printf "The test_update environment: %a\n" pretty_df_env API.test_update ;;

let () = Format.printf "The test environment: %a\n" pretty_df_env API.test_env ;;

let data = read_int_matrix_from_csv "breast-cancer-wisconsin.data" ;;
let actual_data = API.discard_first data ;;

let () = Format.printf "first part of data without the first column: %d\n" (List.hd (List.hd actual_data))
let normalized_data = API.normalizeIntData actual_data ;;
let () = Format.printf "first 10 rows of normalized data without the first column: \n%a\n" ( pretty_matrix 10 10) normalized_data ;; 

let () = Random.self_init()

let randomStream = mkIndexedStream 0 (Obj.magic (API.random_float_vector ())) ;;
let fvals = fst(streamtake 5 randomStream) ;;
let () = Format.printf "random list : %a\n" (pretty_blist pp_print_float) fvals ;;

let init_env = init_env2 9 15 1 (char_list_of_string "w") (char_list_of_string "b") 
    (Obj.magic (random_float_matrix ())) (Obj.magic (random_float_matrix ())) ;;
let () = Format.printf "Init environment: %a\n" pretty_df_env init_env ;;

let wval = eval_wisconsin_batch 10 (Obj.magic init_env) (Obj.magic normalized_data) ;;
let () = Format.printf "wisconsin init loss value : %a\n" (pretty_blist pp_print_float) (Obj.magic wval) ;;

let wval2 = wisconsin_test 10 100 (Obj.magic init_env) (Obj.magic normalized_data) ;;
let () = Format.printf "wisconsin loss value : %a\n" (pretty_blist pp_print_float) (Obj.magic wval2) ;;
(*
let wenv = wisconsin_test_env 6 10 (Obj.magic init_env) (Obj.magic normalized_data) ;;
let () = Format.printf "wisconsin test env: %a\n" pretty_df_env wenv ;;

let nnval = nn_test_val ;;
let () = Format.printf "nn test init loss value : %a\n" (pretty_blist pp_print_float) (Obj.magic nnval) ;;

let wval3 = nn_test 1 ;;
let () = Format.printf "NN test loss value : %a\n" (pretty_blist pp_print_float) (Obj.magic wval3) ;;

let wenv3 = nn_test_env 1 ;;
let () = Format.printf "NN test env: %a\n" pretty_df_env wenv3 ;;

let wenv4 = nn_test_gradenv ;;
let () = Format.printf "NN gradenv env: %a\n" pretty_df_env wenv4 ;;

let wenv5 = nn_test_gradenv_tree ;;
let () = Format.printf "NN gradenv env tree: %a\n" pretty_df_env wenv5 ;;
*)
(*
let gradenvtree = wisconsin_gradenv_tree 1 (Obj.magic init_env) (Obj.magic normalized_data) ;;
let () = Format.printf "wisconsin gradenv_tree : %a\n" pretty_df_env gradenvtree ;;

let gradenv = wisconsin_gradenv 1 (Obj.magic init_env) (Obj.magic normalized_data) ;;
let () = Format.printf "wisconsin gradenv : %a\n" pretty_df_env gradenv ;;
*)







