module ES = Evarsolve

type unif = Logger.log * ES.unification_result

type stats = {
  unif_problems : Big_int.big_int;
  instantiations : Big_int.big_int
}

type unify_fun =
  Environ.env -> Evd.evar_map ->
  Reduction.conv_pb -> EConstr.t -> EConstr.t -> Evarsolve.unification_result

val unify_evar_conv : TransparentState.t -> unify_fun

(** Given a set of evars s and terms t1 t2, it unifies the terms only
    allowing instantiations from the evars in t1 and s, and only
    allowing reduction on the t2. The idea is that t1 acts as a
    "pattern" (for pattern matching), so only the variables in t1 are
    instantiated, as long as they occur in s, and only the scrutinee
    (t2) is reduced.  *)

val unify_match : Evar.Set.t -> TransparentState.t -> unify_fun

(** Same as unify_match but with no reduction *)
val unify_match_nored : Evar.Set.t -> TransparentState.t -> unify_fun

(** Instantiates an evar `?x[subst] args` with a term `t` *)
val instantiate : ?conv_t:Reduction.conv_pb ->
                  ?unify_types:bool ->
                  Environ.env ->
                  EConstr.t Constr.pexistential * EConstr.t list ->
                  EConstr.t ->
                  Evd.evar_map -> ES.unification_result

val get_stats : unit -> stats

(** Mtac execution of tactics *)
val set_run : (Environ.env ->
               Evd.evar_map ->
               EConstr.constr -> (Evd.evar_map * EConstr.t) option) -> unit
val set_lift_constr : (Environ.env -> Evd.evar_map -> Evd.evar_map * EConstr.t) -> unit
