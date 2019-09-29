open Format

open NnoptExtracted.API
open Util
open Pretty

let () = Format.printf "Result of running opt: %a\n" (pretty_visible_option pretty_df_env) opt ;;
let () = Format.printf "The test environment: %a" pretty_df_env test_env 
