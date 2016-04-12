(***********************************************************)
(* Unicoq plugin.                                          *)
(* Copyright (c) 2015 Beta Ziliani <beta@mpi-sws.org>      *)
(*                    Matthieu Sozeau <mattam@mattam.org>. *)
(***********************************************************)

(** Unicoq - An improved unification algorithm for Coq

    This defines a tactic [munify x y] that unifies two typable terms.
*)

(* These are necessary for grammar extensions like the one at the end 
   of the module *)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

DECLARE PLUGIN "unicoq"

open Pp
open Proofview
open Notations
open Munify

let munify_tac gl x y =
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let evars evm = V82.tactic (Refiner.tclEVARS evm) in
  let res = 
    let ts = Conv_oracle.get_transp_state (Environ.oracle env) in
    unify_evar_conv ts env sigma Reduction.CUMUL x y in
    match res with
    | Evarsolve.Success evm -> evars evm
    | Evarsolve.UnifFailure _ -> Tacticals.New.tclFAIL 0 (str"Unification failed")

(* This adds an entry to the grammar of tactics, similar to what
   Tactic Notation does. *)

TACTIC EXTEND munify_tac
| ["munify" constr(c) constr(c') ] ->
  [ Proofview.Goal.enter begin fun gl ->
    let gl = Proofview.Goal.assume gl in
      munify_tac gl c c'
  end
    ]
END

VERNAC COMMAND EXTEND PrintMunifyStats CLASSIFIED AS SIDEFF
  | [ "Print" "Unicoq" "Stats" ] -> [
      let s = Munify.get_stats () in
      Printf.printf "STATS:\t%s\t\t%s\n" 
        (Big_int.string_of_big_int s.unif_problems) 
        (Big_int.string_of_big_int s.instantiations)
  ]
END
