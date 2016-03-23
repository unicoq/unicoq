type unif = 
    Success of Logger.log * Evd.evar_map 
  | Err of Logger.log

type stats = {
  unif_problems : Big_int.big_int;
  instantiations : Big_int.big_int
}

val unify_constr : ?conv_t:Evd.conv_pb ->
  Names.transparent_state ->
  Environ.env ->
  Term.constr -> Term.constr -> Logger.log * Evd.evar_map -> unif

val unify_evar_conv : Names.transparent_state -> Evarsolve.conv_fun

val get_stats : unit -> stats
