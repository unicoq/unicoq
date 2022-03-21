(***********************************************************)
(* Unicoq plugin.                                          *)
(* Copyright (c) 2015 Beta Ziliani <beta@mpi-sws.org>      *)
(*                    Matthieu Sozeau <mattam@mattam.org>. *)
(***********************************************************)

open Pp
open EConstr
open Names
open Vars
open CErrors
open Structures

(* Warning 40 warns about OCaml picking a type for an unknown constructor.  In
   our case, we want OCaml to pick the constructors from Constr.kind_of_term
   without having to write e.g. Constr.App and without importing all of
   Constr. *)
[@@@ocaml.warning "-40"]

module RO = Reductionops
module R = Reduction
module EU = Evarutil
module ES = Evarsolve
module EC = Evarconv
module CND = Context.Named.Declaration
module CRD = Context.Rel.Declaration
module PE = Pretype_errors

let crd_of_tuple (x,y,z) = match y with
  | Some y -> CRD.LocalDef(x,y,z)
  | None   -> CRD.LocalAssum(x,z)

(** {2 Options for unification} *)

(** {3 Enabling Unicoq (implementation at the end) *)
let munify_on = ref false

(** {3 Debugging} *)
let debug = ref false

let set_debug b =
  debug := b

let get_debug () = !debug

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = false;
  Goptions.optkey   = ["Unicoq";"Debug"];
  Goptions.optread  = get_debug;
  Goptions.optwrite = set_debug
}

let trace = ref false
let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = false;
  Goptions.optkey   = ["Unicoq";"Trace"];
  Goptions.optread  = (fun () -> !trace);
  Goptions.optwrite = (fun b -> trace := b);
}

let dump = ref false
let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = false;
  Goptions.optkey   = ["Unicoq";"Dump";"Equalities"];
  Goptions.optread  = (fun () -> !dump);
  Goptions.optwrite = (fun b -> dump := b);
}

let latex_file = ref ""
let _ = Goptions.declare_string_option {
  Goptions.optdepr = false;
  Goptions.optkey = ["Unicoq";"LaTex";"File"];
  Goptions.optread = (fun () -> !latex_file);
  Goptions.optwrite = (fun s-> latex_file := s);
}

(** {3 Rule switches for the algorithm} *)


type options = {
    inst_beta_reduce_type : bool;
    inst_unify_types : bool;
    inst_aggressive : bool;
    inst_super_aggressive : bool;
    inst_try_solving_eqn : bool;
    use_hash : bool
}

let default_options = ref {
    inst_beta_reduce_type = true;
    inst_unify_types = true;
    inst_aggressive = true;
    inst_super_aggressive = false;
    inst_try_solving_eqn = false;
    use_hash = false
}

let current_options () = !default_options

let is_aggressive () = !default_options.inst_aggressive
let set_aggressive b = default_options :=
                         {!default_options with inst_aggressive = b}

let is_super_aggressive () = !default_options.inst_super_aggressive
let set_super_aggressive b =
  if b then
    default_options :=
      {!default_options with inst_aggressive = b; inst_super_aggressive = b}
  else
    default_options :=
      {!default_options with inst_super_aggressive = b}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optkey = ["Unicoq"; "Aggressive"];
  Goptions.optread = is_aggressive;
  Goptions.optwrite = set_aggressive;
}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optkey = ["Unicoq"; "Super"; "Aggressive"];
  Goptions.optread = is_super_aggressive;
  Goptions.optwrite = set_super_aggressive;
}


let get_solving_eqn () = !default_options.inst_try_solving_eqn
let set_solving_eqn b =
  default_options :=
    {!default_options with inst_try_solving_eqn = b}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = false;
  Goptions.optkey   = ["Unicoq"; "Try"; "Solving";"Eqn"];
  Goptions.optread  = get_solving_eqn;
  Goptions.optwrite = set_solving_eqn
}

(** {3 Hashing of failed unifications} *)
let use_hash () = !default_options.use_hash
let set_hash b =
  default_options :=
    {!default_options with use_hash = b}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optkey = ["Unicoq"; "Use";"Hash"];
  Goptions.optread = use_hash;
  Goptions.optwrite = set_hash;
}


(** {2 Stats}

    We log all the calls to unification and the evar instantiations. *)
type my_stats = {
  mutable unif_problems : Int64.t;
  mutable instantiations : Int64.t
}

let dstats = { unif_problems = 0L;
               instantiations = 0L }

type stats = {
  unif_problems : Int64.t;
  instantiations : Int64.t
}

let get_stats () = {
  unif_problems = dstats.unif_problems;
  instantiations = dstats.instantiations
}


(** {2 Functions borrowed from Coq 8.4 and not found in 8.5} *)
(* Note: let-in contributes to the instance *)
let make_evar_instance sigma sign args =
  let rec instrec = function
    | def :: sign, c::args when isVarId sigma (CND.get_id def) c -> instrec (sign,args)
    | def :: sign, c::args -> (CND.get_id def,c) :: instrec (sign,args)
    | [],[] -> []
    | [],_ | _,[] -> anomaly (str"Signature and its instance do not match")
  in
  instrec (sign,args)

let instantiate_evar sigma sign c args =
  let inst = make_evar_instance sigma sign args in
  if inst = [] then c else replace_vars inst c
(** Not in 8.5 *)


(** {2 Generic utility functions} *)
let _array_mem_from_i e i a =
  let j = ref i in
  let length = Array.length a in
  let b = ref false in
  while !j < length && not !b do
    if a.(!j) = e then
      b := true
    else
      j := !j+1
  done;
  !b

let array_mem_to_i e i a =
  let j = ref 0 in
  let b = ref false in
  while !j < i && not !b do
    if a.(!j) = e then
      b := true
    else
      j := !j+1
  done;
  !b

(** Standard monadic operations over option types. *)
let (>>=) opt f =
  match opt with
  | Some(x) -> f x
  | None -> None

let return x = Some x


(** {2 The return type of unification} *)

(** The type of returned values by the algorithm. *)
type unif = Logger.log * ES.unification_result

(** Returns Success after logging it. *)
let success (l, sigma) =
  let l = Logger.reportSuccess l in
  (l, ES.Success sigma)

(** Returns Err after logging it. *)
let err (l, sigma) =
  let l = Logger.reportErr l in
  (l, ES.UnifFailure (sigma, PE.NotSameHead))

(** Logs a success or an error according to s. *)
let report (l, s) =
  match s with
  | ES.Success sigma -> success (l, sigma)
  | ES.UnifFailure (sigma, _) -> err (l, sigma)

let is_success s = match s with ES.Success _ -> true | _ -> false

(** {3 Monadic style operations for the unif type} *)
let (&&=) (l, s as opt) f =
  match s with
  | ES.Success sigma -> f (l, sigma)
  | _ -> opt

let (||=) (l, s as opt) f =
  match s with
  | ES.UnifFailure _ -> f l
  | _ -> opt

let ise_list2 f l1 l2 =
  let rec ise_list2 l1 l2 (l, evd) =
    match l1,l2 with
      [], [] -> (l, ES.Success evd)
    | x::l1, y::l2 ->
      f x y (l, evd) &&= ise_list2 l1 l2
    | _ -> (l, ES.UnifFailure (evd, PE.NotSameHead)) in
  ise_list2 l1 l2

let ise_array2 f v1 v2 evd =
  let l1 = Array.length v1 in
  let l2 = Array.length v2 in
  assert (l1 <= l2) ;
  let diff = l2 - l1 in
  let rec allrec n (l, evdi) =
    if n >= l1 then (l, ES.Success evdi)
    else
      f v1.(n) v2.(n+diff) (l, evdi) &&=
      allrec (n+1)
  in
  allrec 0 evd


(** {2 Functions for debugging} *)

let latexify s =
  let open Str in
  let s = global_replace (regexp "\\\\") "\\\\\\\\" s in
  let s = global_replace (regexp "{") "\\{" s in
  let s = global_replace (regexp "}") "\\}" s in
  let s = global_replace (regexp "%") "\\%" s in
  let s = global_replace (regexp "#") "\\#" s in
  let s = global_replace (regexp "__:=") "" s in (* remove useless names in evar subs *)
  global_replace (Str.regexp "~") "\\~" s

let log_eq env rule conv_t t1 t2 (l, sigma) =
  if not (get_debug () || !trace) then
    (l, ES.Success sigma)
  else
    let ppcmd_of env (t : EConstr.t) =
      try Printer.pr_econstr_env env sigma t
      (* This is really suspicious as it will hide a serious bug. *)
      with _ -> Termops.Internal.debug_print_constr t
    in
    let str1 = Pp.string_of_ppcmds (ppcmd_of env t1) in
    let str2 = Pp.string_of_ppcmds (ppcmd_of env t2) in
    let str1 = latexify str1 in
    let str2 = latexify str2 in
    let l = Logger.newNode !trace (rule, (conv_t, str1, str2)) l in
    (l, ES.Success sigma)

let log_eq_spine env rule conv_t t1 t2 (l, sigma as dsigma) =
  if not (get_debug () || !trace) then
    (l, ES.Success sigma)
  else
    log_eq env rule conv_t (applist t1) (applist t2) dsigma

let debug_str s _l =
  if !debug then
    begin
      Printf.printf "%s\n" s;
      flush_all ()
    end
  else
    ()

let debug_eq env sigma t c1 c2 _l =
  let s1 = string_of_ppcmds (Printer.pr_econstr_env env sigma (applist c1)) in
  let s2 = string_of_ppcmds (Printer.pr_econstr_env env sigma (applist c2)) in
  Printf.printf "%s %s %s\n" s1 (if t == R.CONV then "=?=" else "<?=") s2;
  flush_all ()

let print_eq f (conv_t, c1, c2) =
  output_string f "\\lstinline{";
  output_string f c1;
  output_string f "}~\\approx_{";
  output_string f (if conv_t == R.CONV then "=" else "\\leq");
  output_string f "}~\\lstinline{";
  output_string f c2;
  output_string f "}"


(** {2 Run function for executing arbitrary code given a certain constr}
    This is used in Beta's thesis, although it isn't fully studied.
    We leave it for now, but it might get GC at some point. *)
let run_function = ref (fun _ _ _ -> None)
let set_run f = run_function := f

let lift_constr = ref (fun _ sigma -> sigma, mkProp)
let set_lift_constr c = lift_constr := c

let is_lift env sigma c =
  let sigma, c' = !lift_constr env sigma in
  try eq_constr_nounivs sigma c c'
  with Not_found -> false


(** {2 Utilities for constrs} *)

(** Given a named_context returns a list with its variables *)
let id_substitution nc =
  List.fold_right (fun d s -> mkVar (CND.get_id d) :: s) nc []

(** Pre: isVar v1 *)
let _is_same_var sigma v1 v2 = isVar sigma v2 && (destVar sigma v1 = destVar sigma v2)

(** Pre: isRel v1 *)
let _is_same_rel sigma v1 v2 = isRel sigma v2 && destRel sigma v1 = destRel sigma v2

let _is_same_evar sigma i1 ev2 =
  match kind sigma ev2 with
  | Evar (i2, _) -> i1 = i2
  | _ -> false

let isVarOrRel sigma c = isVar sigma c || isRel sigma c

let is_variable_subs sigma = List.for_all (fun c -> isVar sigma c || isRel sigma c)

let is_variable_args sigma = List.for_all (fun c -> isVar sigma c || isRel sigma c)

(** find_unique finds a unique j such that List.nth j s = id. See use
    below to understand test and dest. *)
exception NotUnique
let find_unique test dest id s =
  let (i, j) = List.fold_right (fun c (i, j) ->
    if test c && dest c = id
    then (i+1, j-1)
    else (i, if i > 0 then j else j-1))
    s (0, List.length s)
  in
  if i = 1 then Some j
  else if i > 1 then raise NotUnique
  else  None

let find_unique_var sigma = find_unique (isVar sigma) (destVar sigma)

let find_unique_rel sigma = find_unique (isRel sigma) (destRel sigma)

let has_definition sigma ts env t =
  if isVar sigma t then
    let var = destVar sigma t in
    if not (TransparentState.is_transparent_variable ts var) then
      false
    else
      let v = CND.get_value (Environ.lookup_named var env) in
      match v with
	| Some _ -> true
	| _ -> false
  else if isRel sigma t then
    let n = destRel sigma t in
    let v = CRD.get_value (Environ.lookup_rel n env) in
    match v with
      | Some _ -> true
      | _ -> false
  else if isConst sigma t then
    let c,_ = destConst sigma t in
      TransparentState.is_transparent_constant ts c &&
      Environ.evaluable_constant c env
  else
    false

(** Must have a definition. *)
let get_definition sigma env t : EConstr.t =
  if isVar sigma t then
    let var = destVar sigma t in
    let v = CND.get_value (EConstr.lookup_named var env) in
    match v with
      | Some c -> c
      | _ -> anomaly (str"get_definition for var didn't have definition!")
  else if isRel sigma t then
    let n = destRel sigma t in
    let v = CRD.get_value (EConstr.lookup_rel n env) in
    match v with
      | Some v -> (lift n) v
      | _ -> anomaly (str"get_definition for rel didn't have definition!")
  else if isConst sigma t then
    let c,i = destConst sigma t in
    of_constr @@ Environ.constant_value_in env (c, EInstance.kind sigma i)
  else
    anomaly (str"get_definition didn't have definition!")

(** Given a defined constant/variable c applied to arguments args it
    unfolds c and returns the new head term d applied to the concatenation
    of arguments. *)
let get_def_app_stack sigma env (c, args) =
  let (d, dargs) = decompose_app sigma (get_definition sigma env c) in
  (d, dargs @ args)

let try_unfolding sigma ts env t =
  if has_definition sigma ts env t then
    get_definition sigma env t
  else
    t

(** pre: |ctx| = |subs| and subs and args are both a list of vars or rels.
   ctx is the (named) context of the evar
   t is the term to invert
   subs is the substitution of the evar
   args are the arguments of the evar
   map is an Intmap mapping evars with list of positions.
   Given a problem of the form
     ?e[subs] args = t
   this function returns t' equal to t, except that every free
   variable (or rel) x in t is replaced by
   - If x appears (uniquely) in subs, then x is replaced by Var n, where
     n is the name of the variable in ctx in the position where x was
     found in s.
   - If x appears (uniquely) in args, then x is replaced by Rel j, were
     j is the position of x in args.
   As a side effect, it populates the map with evars that sould be prunned.
   Prunning is needed to avoid failing when there is hope. E.g., the unification
   problem
     ?e[x] = ?e'[x, z]
   is solvable if we prune z from ?e'.  However, this is not the case in the
   following example:
     ?e[x] = ?e'[x, ?e''[z]]
   The problem lies on the two different options: we can either prune the
   second element of the substitution of ?e', or we can prune the one element
   in the substitution of ?e''.  To make the distinction, we use a boolean
   parameter [inside_evar] to mark that we should fail instead of prunning.

   Finally, note in the example above that we can also try instantiating ?e'
   with ?e instead of the other way round, and this is in fact tried by the
   unification algorithm.
*)
let invert map sigma ctx (t : EConstr.t) subs args ev' =
  let sargs = subs @ args in
  let in_subs j = j < List.length ctx in
  let rmap = ref map in
  let rec invert' inside_evar (t : EConstr.t) i =
    match kind sigma t with
      | Var id ->
	find_unique_var sigma id sargs >>= fun j ->
	if in_subs j then
	  let name = CND.get_id (List.nth ctx j) in
	  return (mkVar name)
	else
	  return (mkRel (List.length sargs - j + i))
      | Rel j when j > i->
	find_unique_rel sigma (j-i) sargs >>= fun k ->
	if in_subs k then
	  let name = CND.get_id (List.nth ctx k) in
	  return (mkVar name)
	else
	  return (mkRel (List.length sargs - k + i))

      | Evar (ev, evargs) when Evar.equal ev ev' ->
        None

      | Evar (ev, evargs) ->
	begin
	  let f (j : int) (c : EConstr.t) =
            match invert' true c i with
              | Some c' -> c'
              | _ ->
		if not inside_evar then
		  begin
		    (if not (Evar.Map.mem ev !rmap) then
			rmap := Evar.Map.add ev [j] !rmap
		     else
                        let ls = Evar.Map.find ev !rmap in
			rmap := Evar.Map.add ev (j :: ls) !rmap)
                    ; c
		  end
		else
		  raise Exit
	  in
	  try return (mkEvar (ev, List.mapi f evargs))
	  with Exit -> None
	end
      | _ ->
	try return (map_with_binders sigma succ (fun i c ->
	  match invert' inside_evar c i with
	    | Some c' -> c'
	    | None -> raise Exit) i t)
	with Exit -> None
  in
  (try invert' false t 0 with NotUnique -> None) >>= fun c' ->
  return (!rmap, c')

(** True if at least one (named) var in tm is in vars. *)
let free_vars_intersect sigma tm vars =
  Names.Id.Set.exists (fun v -> List.mem v vars) (Termops.collect_vars sigma tm)

let some_or_prop o =
  match o with
  | None -> EConstr.mkProp
  | Some tm -> tm

(** Removes the positions in the list, and all dependent elements. *)
let remove sigma l pos =
  let l = List.rev l in
  let rec remove' i (l: (Evd.econstr, Evd.etypes) CND.pt list) vs =
    match l with
      | [] -> []
      | (d :: s) ->
        let o = CND.get_value d in
        let t = CND.get_type d in
        let x = CND.get_id d in
        if List.mem i pos
	  || free_vars_intersect sigma t vs
	  || free_vars_intersect sigma (some_or_prop o) vs then
          remove' (i-1) s (x :: vs)
        else
          (d :: remove' (i-1) s vs)
  in List.rev (remove' (List.length l-1) l [])

exception CannotPrune

(** ev is the evar and plist the indices to prune.  from ?ev : T[env]
    it creates a new evar ?ev' with a shorter context env' such that
    ?ev := ?ev'[id_env']. If the prunning is unsuccessful, it throws
    the exception CannotPrune. *)
let rec prune sigma (ev, plist) =
  (* HACK: assume that if ev is defined, then it was already prunned *)
  if Evd.is_defined sigma ev then sigma
  else
  let evi = Evd.find_undefined sigma ev in
  let env = Evd.evar_filtered_context evi in
  let env' = remove sigma env plist in
  let env_val' = (List.fold_right push_named_context_val env'
                    Environ.empty_named_context_val) in
  (* the type of the evar may contain an evar depending on the some of
     the vars that we want to prune, so we need to prune that
     as well *)
  let concl = Evd.evar_concl evi in
  let id_env' = id_substitution env' in
  match invert Evar.Map.empty sigma env' concl id_env' [] ev with
      None -> raise CannotPrune
    | Some (m, concl) ->
      let sigma = prune_all m sigma in
      let concl = Evd.evar_concl evi in
      let sigma, ev' = EU.new_pure_evar env_val' sigma concl in
      Evd.define ev (mkEvar (ev', id_env')) sigma

and prune_all map sigma =
  List.fold_left prune sigma (Evar.Map.bindings map)

(** pre: |s1| = |s2|
    pos: None if s1 or s2 are not equal and not var to var subs
        Some l with l list of indexes where s1 and s2 do not agree *)
let intersect env sigma options s1 s2 =
  let n = Array.length s1 in
  let rec intsct i =
    if i < n then
      intsct (i+1) >>= fun l ->
      if eq_constr sigma s1.(i) s2.(i) then
        Some l
      else
        if (isVar sigma s1.(i) || isRel sigma s1.(i)) &&  (isVar sigma s2.(i) || isRel sigma s2.(i)) then
          Some (i :: l) (* both position holds variables: they are indeed different *)
        else if !options.inst_aggressive then Some (i :: l)
	else None
    else Some []
  in
  assert (Array.length s2 = n) ;
  intsct 0

(** pre: ev is not defined *)
let unify_same dbg env sigma options ev subs1 subs2 =
  match intersect env sigma options subs1 subs2 with
  | Some [] -> (false, (dbg, ES.Success sigma))
  | Some l ->
    begin
      try
        (true, (dbg, ES.Success (prune sigma (ev, l))))
      with CannotPrune -> (false, (dbg, ES.UnifFailure (sigma, PE.NotSameHead)))
    end
  | _ -> (false, (dbg, ES.UnifFailure (sigma, PE.NotSameHead)))

(** given a list of arguments [args] = [x1 .. xn], a [body] with free
    indices [1 .. n], and a substitution [subst] with context [nc] it
    returns [fun x1 : A1{subst}^-1 => .. => fun xn : An{subst}^-1 =>
    body], where each [A_i] is the type of [x_i].
*)
let fill_lambdas_invert_types map env sigma nc body subst args ev =
  let rmap = ref map in
  List.fold_right (fun arg r-> r >>= fun (ars, bdy) ->
    let ty = Retyping.get_type_of env sigma arg in
    let ars = CList.drop_last ars in
    invert map sigma nc ty subst ars ev >>= fun (m, ty) ->
    rmap := m;
    let n = Namegen.named_hd env sigma ty Anonymous in
    return (ars, mkLambda (Context.make_annot n Sorts.Relevant, ty, bdy))) args (return (args, body))
  >>= fun (_, bdy) -> return (!rmap, bdy)

exception ProjectionNotFound
(* [check_conv_record (t1,l1) (t2,l2)] tries to decompose the problem
   (t1 l1) = (t2 l2) into a problem

   l1 = params1@c1::extra_args1
   l2 = us2@extra_args2
   (t1 params1 c1) = (proji params (c xs))
   (t2 us2) = (cstr us)
   extra_args1 = extra_args2

   by finding a record R and an object c := [xs:bs](Build_R params v1..vn)
   with vi = (cstr us), for which we know that the i-th projection proji
   satisfies

   (proji params (c xs)) = (cstr us)

   Rem: such objects, usable for conversion, are defined in the objdef
   table; practically, it amounts to "canonically" equip t2 into a
   object c in structure R (since, if c1 were not an evar, the
   projection would have been reduced) *)

let check_conv_record env sigma (t1,l1) (t2,l2) =
  try
    let (proji,_inst), l1 = try
        Termops.global_of_constr sigma t1, l1
      with Not_found ->
        let t1, r1 = try destProj sigma t1 with Constr.DestKO -> raise Not_found in
        let app = Retyping.expand_projection env sigma t1 r1 l1 in
        let t1, l1 = destApp sigma app in
        let c1, inst = destConst sigma t1 in
        let gr1 = GlobRef.ConstRef c1 in
        (gr1, inst), Array.to_list l1
    in
    let (sigma, solution), l2_effective =
      try
        let open ValuePattern in
        match kind sigma t2 with
            Prod (_,a,b) -> (* assert (l2=[]); *)
                    if Termops.dependent sigma (mkRel 1) b then raise Not_found
              else CanonicalSolution.find env sigma (proji, Prod_cs),[a;Termops.pop b]
          | Sort s ->
              CanonicalSolution.find env sigma
                (proji, Sort_cs (Sorts.family (ESorts.kind sigma s))),[]
          | _ ->
              let c2,_ = Termops.global_of_constr sigma t2 in
              CanonicalSolution.find env sigma (proji, Const_cs c2),l2
      with Not_found ->
        CanonicalSolution.find env sigma (proji, Default_cs),[]
    in
    let open CanonicalSolution in
    let params1, c1, extra_args1 =
      match CList.chop solution.nparams l1 with
      | params1, c1::extra_args1 -> params1, c1, extra_args1
      | _ -> raise Not_found in
    let us2,extra_args2 = CList.chop (List.length solution.cvalue_arguments) l2_effective in
    sigma,solution.constant,solution.abstractions_ty,(solution.params,params1),(solution.cvalue_arguments,us2),(extra_args1,extra_args2),c1,
    (solution.cvalue_abstraction,applist(t2,l2))
  with Failure _ | Not_found ->
    raise ProjectionNotFound

let evar_apprec ts env sigma (c, stack) =
  let rec aux s =
    let ((t,stack)) =
      RO.(whd_betaiota_deltazeta_for_iota_state ts env sigma s) in
    match kind sigma t with
    | Evar (evk,eva) when Evd.is_defined sigma evk ->
      aux (Evd.existential_value sigma (evk,eva), stack)
    | _ ->
      match RO.Stack.list_of_app_stack stack with
      | None -> decompose_app sigma (RO.Stack.zip sigma (t, stack))
      | Some stack -> (t, stack)
  in aux (c, RO.Stack.append_app_list stack RO.Stack.empty)

let eq_app_stack sigma (c, l) (c', l') =
  eq_constr sigma c c' && List.for_all2 (eq_constr sigma) l l'

let remove_non_var env sigma (ev, subs as evsubs) args =
  let subs = Array.of_list subs in
  let ps = CArray.fold_right_i (fun i a s ->
    if isVarOrRel sigma a && not (array_mem_to_i a i subs || List.mem a args) then s
    else i::s) subs [] in
  if ps = [] then raise CannotPrune
  else
    let sigma' = prune sigma (ev, ps) in
    (sigma', mkEvar evsubs, args)

let specialize_evar env sigma (ev, subs) args =
  match args with
  | [] -> raise CannotPrune
  | hd :: tl ->
    let sigma', lam = Evardefine.define_evar_as_lambda env sigma (ev, subs) in
    let (n, dom, codom) = destLambda sigma' lam in
      sigma', subst1 hd codom, tl

(* EJGA: Not used *)
(* exception InternalException *)

(** {2 The function} *)

(** Enum type to specify on which side of the equation an action is taken *)
type which_side = Left | Right | Both | NoAction
(* let ws_to_string = function
 *   | Left -> "Left"
 *   | Right -> "Right"
 *   | Both -> "Both"
 *   | NoAction -> "NoAction" *)

(** Enum type indicating if the algorithm must swap the lhs and rhs. *)
type direction = Original | Swap
let switch dir f t u = if dir == Original then f t u else f u t
(* let dir_to_string = function
 *   | Original -> "Original"
 *   | Swap -> "Swap" *)

(** Enum type indicating where it is useless to reduce. *)
type stucked = NotStucked | StuckedLeft | StuckedRight

(** Input parameters for the algorithm *)
module type Params = sig
  val flags : Evarsolve.unify_flags
  val wreduce : which_side (* on which side it must perform reduction *)
  val winst : which_side (* on which side evars are allowed to be instantiated *)
  val match_evars : Evar.Set.t option (* which evars may be instantiated *)
end

type unify_fun =
  Environ.env -> Evd.evar_map ->
  Reduction.conv_pb -> EConstr.t -> EConstr.t -> Evarsolve.unification_result

(** The main module type of unification, containing the functions that can be exported *)
module type Unifier = sig
  val unify_evar_conv : unify_fun

  val unify_constr : ?conv_t:R.conv_pb ->
                     ?options:options ref ->
                     Environ.env ->
                     EConstr.t -> EConstr.t -> Logger.log * Evd.evar_map -> unif

  val instantiate : R.conv_pb ->
           options ref ->
           Environ.env ->
           EConstr.t Constr.pexistential * EConstr.t list ->
           EConstr.t * EConstr.t list ->
           Evd.evar_map -> ES.unification_result
end

module type UnifT = functor (P : Params) -> Unifier

(** Side module for instnatiation of evars. In certain cases we need
    to call it with specific parameters, and this is why it is not
    part of the main module. *)
module Inst = functor (U : Unifier) -> struct

  (** Removes the equal variables of args and args', starting from the
      right most argument, until a different variable is found.
      (Avoids unnecessary eta-expansions.) It needs to check that no
      solution is lost, meaning that the variable being removed is not
      duplicated in any of the spines or bodies. *)
  let remove_equal_tail sigma (h, args) (h', args') =
    let rargs = List.rev args in
    let rargs' = List.rev args' in
    let noccur sigma i xs ys =
      not (Termops.dependent sigma i h')
      && not (Termops.dependent sigma i h)
      && not (List.exists (Termops.dependent sigma i) ys)
      && not (List.exists (Termops.dependent sigma i) xs) in
    let rec remove rargs rargs' =
      match rargs, rargs' with
      | (x :: xs), (y :: ys) when eq_constr sigma x y && noccur sigma x xs ys -> remove xs ys
      | _, _ -> rargs, rargs'
    in
    let (xs, ys) = remove rargs rargs' in
    (List.rev xs, List.rev ys)

  (* pre: args and args' are lists of vars and/or rels. subs is an array of rels and vars. *)
  let instantiate' dir options conv_t env (ev, subs as uv) args (h, args') (dbg, sigma0) =
    let args, args' = remove_equal_tail sigma0 (mkEvar uv, args) (h, args') in
    (* beta-reduce to remove dependencies *)
    let t = if !options.inst_beta_reduce_type then
              RO.whd_beta env sigma0 (applist (h, args'))
            else (applist (h, args')) in
    let evi = Evd.find_undefined sigma0 ev in
    let nc = Evd.evar_filtered_context evi in
    let res =
      let subsl = subs in
      invert Evar.Map.empty sigma0 nc t subsl args ev >>= fun (map, t') ->
      fill_lambdas_invert_types map env sigma0 nc t' subsl args ev >>= fun (map, t') ->
      let sigma = prune_all map sigma0 in
      let sigma, t' =
	Evarsolve.refresh_universes
	    (if conv_t == R.CUMUL && isArity sigma t' then
	      (* ?X <= Type(i) -> X := Type j, j <= i *)
	      (* Type(i) <= X -> X := Type j, i <= j *)
	      Some (dir == Original)
	   else None)
	    (EConstr.push_named_context nc env) sigma t' in
      let t'' = instantiate_evar sigma nc t' subsl in
      (* XXX: EConstr.API *)
      let ty = Evd.existential_type sigma (ev,subs) in
      let unifty =
	try
	  match kind sigma t'' with
	  | Evar (evk2, _) ->
            (* ?X : Π Δ. Type i = ?Y : Π Δ'. Type j.
	       The body of ?X and ?Y just has to be of type Π Δ. Type k for some k <= i, j. *)
	    let evienv = Evd.evar_env env evi in
	    let ctx1, i = R.dest_arity evienv (EConstr.to_constr ~abort_on_undefined_evars:false sigma evi.Evd.evar_concl) in
	    let evi2 = Evd.find sigma evk2 in
	    let evi2env = Evd.evar_env env evi2 in
	    let ctx2, j = R.dest_arity evi2env (EConstr.to_constr ~abort_on_undefined_evars:false sigma evi2.Evd.evar_concl) in
	    if i == j || Evd.check_eq sigma i j then (* Shortcut, i = j *)
	      (dbg, ES.Success sigma)
	    else if Evd.check_leq sigma i j then
              let t2 = it_mkProd_or_LetIn (mkSort i) (List.map of_rel_decl ctx2) in
	      (dbg, ES.Success (Evd.downcast evk2 t2 sigma))
            else if Evd.check_leq sigma j i then
	      let t1 = it_mkProd_or_LetIn (mkSort j) (List.map of_rel_decl ctx1) in
              (dbg, ES.Success (Evd.downcast ev t1 sigma))
	    else
              let sigma, k = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
	      let t1 = it_mkProd_or_LetIn (mkSort k) (List.map of_rel_decl ctx1) in
	      let t2 = it_mkProd_or_LetIn (mkSort k) (List.map of_rel_decl ctx2) in
	      let sigma = Evd.set_leq_sort env (Evd.set_leq_sort env sigma k i) k j in
	      (dbg, ES.Success (Evd.downcast evk2 t2 (Evd.downcast ev t1 sigma)))
	  | _ -> raise R.NotArity
	  with R.NotArity ->
            if !options.inst_unify_types then begin
                let ty' = Retyping.get_type_of env sigma t'' in
                U.unify_constr ~conv_t:R.CUMUL env ty' ty (dbg, sigma)
              end
            else
              (dbg, ES.Success sigma)
              
	in
	let p = unifty &&= fun (dbg, sigma) ->
	    if Termops.occur_meta sigma t' (* || Termops.occur_evar ev t' *) then
	      (dbg, ES.UnifFailure (sigma0, PE.NotSameHead))
	    else
	      (dstats.instantiations <- Int64.succ dstats.instantiations;
	       (dbg, ES.Success (Evd.define ev t' sigma)))
	in
	  Some p
    in
    match res with
    | Some r -> r
    | None -> (dbg, ES.UnifFailure (sigma0, PE.NotSameHead))
end

(** forward the use of evar conv's compare heads *)
let ev_compare_heads env nparams1 t1 t2 (dbg, sigma) : unif =
  (dbg, EC.compare_heads env sigma ~nargs:nparams1 t1 t2)

(** {3 Hashing table of failures} *)
let tbl = Hashtbl.create 1000

(** The main module *)
let rec unif (module P : Params) : (module Unifier) = (
module struct

  (** If evar e can be instantiated:
      1) It must be in match_evars (assuming match_evars is Some set).
      2) The instantiation matches the direction in which it is being performed.
  *)
  let must_inst (dir: direction) (e: Evar.t) =
    Option.cata (Evar.Set.mem e) true P.match_evars &&
    (P.winst == Both
    || (P.winst == Left && dir == Original)
    || (P.winst == Right && dir == Swap))

  (** If reduction is allowed to happen on the lhs. *)
  let reduce_left = P.wreduce == Left || P.wreduce == Both

  (** If reduction is allowed to happen on the rhs. *)
  let reduce_right = P.wreduce == Right || P.wreduce == Both

  let tblfind t x = try Hashtbl.find t x with Not_found -> false

  let try_hash env sp1 sp2 (dbg, sigma as dsigma) =
    if use_hash () && tblfind tbl (sigma, env, sp1, sp2) then
      begin
        log_eq_spine env "Hash-Hit" R.CONV sp1 sp2 dsigma &&= fun (dbg, sigma) ->
          report (dbg, ES.UnifFailure (sigma, PE.NotSameHead))
      (* TODO Something is funky here: it returns error on a success
         and the other way around?? *)
      end
    else
      (dbg, ES.Success sigma)

  (** {3 Conversion check} *)
  let ground_spine sigma (h, args) =
    EU.is_ground_term sigma h && List.for_all (EU.is_ground_term sigma) args

  let try_conv conv_t env (c1, l1 as sp1) (c2, l2 as sp2) (dbg, sigma0) =
    if P.wreduce == Both && ground_spine sigma0 sp1 && ground_spine sigma0 sp2 then
      let app1 = applist sp1 and app2 = applist sp2 in
      try
        begin match RO.infer_conv ~pb:conv_t ~ts:P.flags.closed_ts env sigma0 app1 app2 with
        | None -> (dbg, ES.UnifFailure (sigma0, PE.NotSameHead))
        | Some sigma1 ->
          report (log_eq_spine env "Reduce-Same" conv_t sp1 sp2 (dbg, sigma1))
        end
      with Univ.UniverseInconsistency _ -> (dbg, ES.UnifFailure (sigma0, PE.NotSameHead))
    else (dbg, ES.UnifFailure (sigma0, PE.NotSameHead))


(* let debug_env env sigma c = *)
(*   if !dump then  *)
(*     Feedback.msg_debug (Printer.pr_econstr_env env sigma c) *)
(* let debug c = *)
(*   if !dump then  *)
(*     Feedback.msg_debug (Printer.pr_econstr c) *)
        
  (** Given a head term c and with arguments l it whd reduces c if it is
      an evar, returning the new head and list of arguments.
  *)
  let rec decompose_evar sigma (c, l) =
    let (c', l') = decompose_app sigma c in
    if isCast sigma c' then
      let (t, _, _) = destCast sigma c' in
      decompose_evar sigma (t, l' @ l)
    else
      (c', l' @ l)

  (** {3 "The Function" is split into several} *)
  let rec unify'' ?(conv_t=R.CONV) ?(options=default_options) cont env t t' (dbg, sigma) =
    assert (not (isApp sigma (fst t) || isApp sigma (fst t')));
    let (c, l as t) = decompose_evar sigma t in
    let (c', l' as t') = decompose_evar sigma t' in
    if !dump then debug_eq env sigma conv_t t t' 0;
    try_conv conv_t env t t' (dbg, sigma) ||= fun dbg ->
      try_hash env t t' (dbg, sigma) &&= fun (dbg, sigma) ->
        let res =
          if isEvar sigma c || isEvar sigma c' then
            one_is_meta dbg conv_t env sigma options t t'
          else
            begin
              try_run_and_unify env t t' (dbg, sigma)
              ||= try_canonical_structures env t t' sigma
              ||= try_app_fo conv_t env t t' sigma
              ||= cont conv_t env t t' sigma
            end
        in
        if not (is_success (snd res)) && use_hash () then
          Hashtbl.add tbl (sigma, env, t, t') true;
        res

  and unify' ?(conv_t=R.CONV) ?(options=default_options) =
    unify'' ~conv_t ~options (fun conv_t env t t' sigma dbg -> try_step conv_t env t t' (dbg, sigma))

  and unify_constr ?(conv_t=R.CONV) ?(options=default_options) env t t' (dbg, sigma) =
    unify' ~conv_t ~options env (decompose_app sigma t) (decompose_app sigma t') (dbg,sigma)

  and unify_evar_conv env sigma0 conv_t t t' =
    let interesting log = (* if it's not just Reduce-Same *)
      match !log with
      | Logger.Node (("Reduce-Same", _), _, true, _) -> false
      | _ -> true in
    dstats.unif_problems <- Int64.succ dstats.unif_problems;
    if use_hash () then Hashtbl.clear tbl;
    match unify_constr ~conv_t:conv_t env t t' (Logger.init, sigma0) with
    | (log, ES.Success sigma') ->
      if get_debug () && interesting log then
        begin
          Logger.print_latex !latex_file print_eq log;
          Logger.print_to_stdout log;
        end
      else ();
      ES.Success sigma'
    | (log, ES.UnifFailure (sigma, e)) ->
      if get_debug () then Logger.print_to_stdout log;
      ES.UnifFailure (sigma, e)

  (** (Beta) This is related to Mtac, and is part of my thesis. The
      idea is to allow for the execution of (arbitrary) code during
      unification. At some point I need to either remove this, or
      prove it is an useful thing to have... *)
  and try_run_and_unify env (c, l as t) (c', l' as t') (dbg, sigma) =
    if (isConst sigma c || isConst sigma c') && not (eq_constr sigma c c') then
      begin
        if is_lift env sigma c && List.length l = 3 then
	  run_and_unify dbg env sigma l t'
        else if is_lift env sigma c' && List.length l' = 3 then
	  run_and_unify dbg env sigma l' t
        else
	  (dbg, ES.UnifFailure (sigma, PE.NotSameHead))
      end
    else
      (dbg, ES.UnifFailure (sigma, PE.NotSameHead))

  and run_and_unify dbg env sigma0 args ty =
    let a, f, v = List.nth args 0, List.nth args 1, List.nth args 2 in
    unify' ~conv_t:R.CUMUL env (decompose_app sigma0 a) ty (dbg, sigma0) &&= fun (dbg, sigma1) ->
      match !run_function env sigma1 f with
      | Some (sigma2, v') -> unify' env (decompose_app sigma2 v) (decompose_app sigma2 v') (dbg, sigma2)
      | _ -> (dbg, ES.UnifFailure (sigma1, PE.NotSameHead))

  and try_canonical_structures env (c, _ as t) (c', _ as t') sigma dbg =
    if (isConst sigma c || isConst sigma c' || isProj sigma c || isProj sigma c')
        && not (eq_constr sigma c c') then
      try conv_record dbg env sigma t t'
      with ProjectionNotFound ->
      try conv_record dbg env sigma t' t
      with ProjectionNotFound -> (dbg, ES.UnifFailure (sigma, PE.NotSameHead))
    else
      (dbg, ES.UnifFailure (sigma, PE.NotSameHead))

  and conv_record dbg env evd t t' =
    let (evd,c,bs,(params,params1),(us,us2),(ts,ts1),c1,(n,t2)) = check_conv_record env evd t t' in
    let (evd',ks,_) =
      List.fold_left
        (fun (i,ks,m) b ->
	   match n with
           | Some n when m = n -> (i,t2::ks, m-1)
           | _ ->
             let dloc = Loc.tag @@ Evar_kinds.InternalHole in
             let sigma = i in
             let sigma, ev = Evarutil.new_evar env sigma ~src:dloc (substl ks b) in
             (sigma, ev :: ks, m - 1))
        (evd,[],List.length bs) bs
    in
    report (
      log_eq_spine env "CS" R.CONV t t' (dbg, evd') &&=
      ise_list2 (fun x1 x -> unify_constr env x1 (substl ks x)) params1 params &&=
      ise_list2 (fun u1 u -> unify_constr env u1 (substl ks u)) us2 us &&=
      unify' env (decompose_app evd' c1) (c,(List.rev ks)) &&=
      ise_list2 (unify_constr env) ts ts1)

  and try_app_fo conv_t env (c, l as t) (c', l' as t') sigma dbg =
    let nparams = List.length l in
    if nparams = List.length l' then
      begin
        report (
          log_eq_spine env "App-FO" conv_t t t' (dbg, sigma) &&=
          compare_heads conv_t env nparams c nparams c' &&=
          ise_list2 (unify_constr env) l l'
        )
      end
    else
      (dbg, ES.UnifFailure (sigma, PE.NotSameHead))

  and one_is_meta dbg conv_t env sigma0 options (c, l as t) (c', l' as t') =
    if isEvar sigma0 c && isEvar sigma0 c' then
      let (k1, s1 as e1), (k2, s2 as e2) = destEvar sigma0 c, destEvar sigma0 c' in
      if k1 = k2 then
        (* Meta-Same *)
        begin
          let (b,p) = unify_same dbg env sigma0 options k1 (Array.of_list s1) (Array.of_list s2) in
          let dbg, sigma = fst p, match snd p with
            | ES.Success sigma -> sigma
            | ES.UnifFailure (sigma, _) -> sigma
          in
          let rule = if b then "Meta-Same" else "Meta-Same-Same" in
          log_eq_spine env rule conv_t t t' (dbg, sigma) &&= fun (dbg, sigma) ->
            if is_success (snd p) then
              report (ise_list2 (unify_constr env) l l' (dbg, sigma))
            else
              report (dbg, ES.UnifFailure (sigma, PE.NotSameHead))
        end
      else
        begin
	  (* Meta-Meta: we try both directions, but first the one with the
           longest substitution. *)
          let dir1, dir2, var1, var2, term1, term2 =
            if List.length s1 > List.length s2 then
              Original, Swap, (e1, l), (e2, l'), t', t
            else
              Swap, Original, (e2, l'), (e1, l), t, t'
          in
          meta_inst dir1 options conv_t env var1 term1 sigma0 dbg
          ||= meta_inst dir2 options conv_t env var2 term2 sigma0
          ||= meta_fo dir1 options conv_t env var1 term1 sigma0
          ||= meta_fo dir2 options conv_t env var2 term2 sigma0
          ||= meta_deldeps dir1 options conv_t env var1 term1 sigma0
          ||= meta_deldeps dir2 options conv_t env var2 term2 sigma0
          ||= meta_specialize dir1 options conv_t env var1 term1 sigma0
          ||= meta_specialize dir2 options conv_t env var2 term2 sigma0
          ||= try_solve_simple_eqn options conv_t env var1 term1 sigma0
        end
    else
    if isEvar sigma0 c then
      if is_lift env sigma0 c' && List.length l' = 3 then
        run_and_unify dbg env sigma0 l' t
      else
        begin
          let e1 = destEvar sigma0 c in
          instantiate conv_t env (e1, l) t' (dbg, sigma0)
        end
    else
    if is_lift env sigma0 c && List.length l = 3 then
      run_and_unify dbg env sigma0 l t
    else
      begin
        let e2 = destEvar sigma0 c' in
        instantiate ~dir:Swap conv_t env (e2, l') t (dbg, sigma0)
      end
  and try_solve_simple_eqn ?(dir=Original) options conv_t env (evsubs, args) t sigma dbg =
    if !options.inst_try_solving_eqn then
      try
        (* TODO: Why the [] here!! *)
        let t = ES.solve_pattern_eqn env sigma [] (applist t) in
        let pbty = match conv_t with
	    R.CONV -> None
          | R.CUMUL -> Some (dir == Original)
        in
        match ES.solve_simple_eqn (fun _flags _k -> unify_evar_conv) P.flags env sigma (pbty, evsubs, t) with
          ES.Success sigma' ->
          Printf.printf "%s" "solve_simple_eqn solved it: ";
	  debug_eq env sigma R.CONV (mkEvar evsubs, []) (decompose_app sigma t) 0;
	  (dbg, ES.Success sigma')
	| e -> (dbg, e)
      with _ ->
        Printf.printf "%s" "solve_simple_eqn failed!";
        (dbg, ES.UnifFailure (sigma, PE.NotSameHead))
    else
      (dbg, ES.UnifFailure (sigma, PE.NotSameHead))

  and compare_heads conv_t env nparams c nparams' c' (dbg, sigma0) =
    let rigid_same sigma = report (log_eq env "Rigid-Same" conv_t c c' (dbg, sigma)) in
    match (kind sigma0 c, kind sigma0 c') with
    (* Type-Same *)
    | Sort s1, Sort s2 ->
      log_eq env "Type-Same" conv_t c c' (dbg, sigma0) &&= fun (dbg, sigma0) ->
        begin
          try
	    let sigma1 = match conv_t with
              | R.CONV -> Evd.set_eq_sort env sigma0 (ESorts.kind sigma0 s1) (ESorts.kind sigma0 s2)
	      | R.CUMUL -> Evd.set_leq_sort env sigma0 (ESorts.kind sigma0 s1) (ESorts.kind sigma0 s2)
            in
            report (dbg, ES.Success sigma1)
          with Univ.UniverseInconsistency e ->
	    debug_str (Printf.sprintf "Type-Same exception: %s"
		  (Pp.string_of_ppcmds (Univ.explain_universe_inconsistency Univ.Level.pr e))) 0;
          report (dbg, ES.UnifFailure (sigma0, PE.NotSameHead))
        end

    (* Lam-Same *)
    | Lambda (name, t1, c1), Lambda (_, t2, c2) ->
      let env' = EConstr.push_rel (crd_of_tuple (name, None, t1)) env in
      report (
        log_eq env "Lam-Same" conv_t c c' (dbg, sigma0) &&=
        unify_constr env t1 t2 &&=
        unify_constr ~conv_t env' c1 c2)

    (* Prod-Same *)
    | Prod (name, t1, c1), Prod (_, t2, c2) ->
      report (
        log_eq env "Prod-Same" conv_t c c' (dbg, sigma0) &&=
        unify_constr env t1 t2 &&=
        let env = EConstr.push_rel (crd_of_tuple (name,None,t1)) env in
        unify_constr ~conv_t env c1 c2)

    | LetIn (name, trm1, ty1, body1), LetIn (_, trm2, ty2, body2) ->
      (* Let-Same *)
      let env' = EConstr.push_rel (crd_of_tuple (name, Some trm1, ty1)) env in
      report (
        log_eq env "Let-Same" conv_t c c' (dbg, sigma0) &&=
        unify_constr env trm1 trm2 &&=
        unify_constr ~conv_t env' body1 body2)

    (* Rigid-Same *)
    | Rel n1, Rel n2 when n1 = n2 ->
      rigid_same sigma0
    | Var id1, Var id2 when Id.equal id1 id2 ->
      rigid_same sigma0
    | Const (c1,_), Const (c2,_) when Constant.equal c1 c2 ->
      report (
        log_eq env "Rigid-Same" conv_t c c' (dbg, sigma0) &&=
        ev_compare_heads env nparams c c')
    | Ind (c1,_), Ind (c2,_) when Names.eq_ind c1 c2 ->
      report (
        log_eq env "Rigid-Same" conv_t c c' (dbg, sigma0) &&=
        ev_compare_heads env nparams c c')
    | Construct (c1,_), Construct (c2,_) when Names.eq_constructor c1 c2 ->
      report (
        log_eq env "Rigid-Same" conv_t c c' (dbg, sigma0) &&=
        ev_compare_heads env nparams c c')

    | Proj (c1, t1), Proj (c2, t2) when Names.Projection.repr_equal c1 c2 ->
      report (
        log_eq env "Proj-Same" conv_t c c' (dbg, sigma0) &&=
        unify_constr env t1 t2)
    | CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2))
      when i1 = i2 ->
      report (
        log_eq env "CoFix-Same" conv_t c c' (dbg, sigma0) &&=
        ise_array2 (unify_constr env) tys1 tys2 &&=
        ise_array2 (unify_constr (push_rec_types_econstr sigma0 recdef1 env)) bds1 bds2)

    | Case (ci1, u1, pms1, p1, iv1, c1, cl1), Case (ci2, u2, pms2, p2, iv2, c2, cl2) ->
      let (ci1, p1, _, c1, cl1) = EConstr.expand_case env sigma0 (ci1, u1, pms1, p1, iv1, c1, cl1) in
      let (ci2, p2, _, c2, cl2) = EConstr.expand_case env sigma0 (ci2, u2, pms2, p2, iv2, c2, cl2) in
      report (
        log_eq env "Case-Same" conv_t c c' (dbg, sigma0) &&=
        unify_constr env p1 p2 &&=
        unify_constr env c1 c2 &&=
        ise_array2 (unify_constr env) cl1 cl2)

    | Fix (li1, (_, tys1, bds1 as recdef1)), Fix (li2, (_, tys2, bds2))
      when li1 = li2 ->
      report (
        log_eq env "Fix-Same" conv_t c c' (dbg, sigma0) &&=
        ise_array2 (unify_constr env) tys1 tys2 &&=
        ise_array2 (unify_constr (push_rec_types_econstr sigma0 recdef1 env)) bds1 bds2)

    | _, _ ->
      (dbg, ES.UnifFailure (sigma0, PE.NotSameHead))

  and push_rec_types_econstr sigma (a, l, m) env =
    Environ.push_rec_types (a, Array.map (to_constr ~abort_on_undefined_evars:false sigma) l, Array.map (to_constr ~abort_on_undefined_evars:false sigma) m) env

  and try_step ?(stuck=NotStucked) conv_t env (c, l as t) (c', l' as t') (dbg, sigma0) =
    match (kind sigma0 c, kind sigma0 c') with
    (* Lam-BetaR *)
    | _, Lambda (_, _, trm) when reduce_right && not (CList.is_empty l') ->
      let (c2, l2) = decompose_app sigma0 (subst1 (List.hd l') trm) in
      let t2 = (c2, l2 @ List.tl l') in
      report (
        log_eq_spine env "Lam-BetaR" conv_t t t' (dbg, sigma0) &&=
        unify' ~conv_t env t t2)

    | _, LetIn (_, trm, _, body) when reduce_right ->
      let (c2, l2) = decompose_app sigma0 (subst1 trm body) in
      let t2 = (c2, l2 @ l') in
      report (
        log_eq_spine env "Let-ZetaR" conv_t t t' (dbg, sigma0) &&=
        unify' ~conv_t env t t2)

    | (_, Case _ | _, Fix _) when reduce_right && stuck != StuckedRight ->
      let t2 = evar_apprec P.flags.open_ts env sigma0 t' in
      if not (eq_app_stack sigma0 t' t2) then
        begin report (
            log_eq_spine env "Case-IotaR" conv_t t t' (dbg, sigma0) &&=
	    unify' ~conv_t env t t2)
	end
      else if stuck = NotStucked then
	try_step ~stuck:StuckedRight conv_t env t t' (dbg, sigma0)
      else (dbg, ES.UnifFailure (sigma0, PE.NotSameHead))

    (* Lam-BetaL *)
    | Lambda (_, _, trm), _ when reduce_left && not (CList.is_empty l) ->
      let (c1, l1) = decompose_app sigma0 (subst1 (List.hd l) trm) in
      let t1 = (c1, l1 @ List.tl l) in
      report (
        log_eq_spine env "Lam-BetaL" conv_t t t' (dbg, sigma0) &&=
        unify' ~conv_t env t1 t')
    (* Let-ZetaL *)
    | LetIn (_, trm, _, body), _ when reduce_left ->
      let (c1, l1) = decompose_app sigma0 (subst1 trm body) in
      let t1 = (c1, l1 @ l) in
      report (
        log_eq_spine env "Let-ZetaL" conv_t t t' (dbg, sigma0) &&=
        unify' ~conv_t env t1 t')

    | (Case _, _ | Fix _, _) when reduce_left && stuck != StuckedLeft ->
      let t2 = evar_apprec P.flags.open_ts env sigma0 t in
      if not (eq_app_stack sigma0 t t2) then
	begin report (
          log_eq_spine env "Case-IotaL" conv_t t t' (dbg, sigma0) &&=
	  unify' ~conv_t env t2 t')
	end
      else if stuck == NotStucked then
	try_step ~stuck:StuckedLeft conv_t env t t' (dbg, sigma0)
      else (dbg, ES.UnifFailure (sigma0, PE.NotSameHead))

    (* Constants get unfolded after everything else *)
    | (_, Const _ | _, Rel _ | _, Var _)
      when reduce_right && has_definition sigma0 P.flags.open_ts env c' && stuck == NotStucked ->
      if is_stuck env sigma0 t' then
        try_step ~stuck:StuckedRight conv_t env t t' (dbg, sigma0)
      else report (
          log_eq_spine env "Cons-DeltaNotStuckR" conv_t t t' (dbg, sigma0) &&=
          unify' ~conv_t env t (evar_apprec P.flags.open_ts env sigma0 (get_def_app_stack sigma0 env t')))
    | (Const _, _ | Rel _, _ | Var _, _)
      when reduce_left && has_definition sigma0 P.flags.open_ts env c && stuck == StuckedRight ->
      report (
        log_eq_spine env "Cons-DeltaStuckL" conv_t t t'  (dbg, sigma0) &&=
        unify' ~conv_t env (evar_apprec P.flags.open_ts env sigma0 (get_def_app_stack sigma0 env t)) t')

    | (_, Const _ | _, Rel _ | _, Var _)
      when reduce_right && has_definition sigma0 P.flags.open_ts env c' ->
      report (
        log_eq_spine env "Cons-DeltaR" conv_t t t' (dbg, sigma0) &&=
        unify' ~conv_t env t (evar_apprec P.flags.open_ts env sigma0 (get_def_app_stack sigma0 env t')))
    | (Const _, _ | Rel _, _ | Var _, _)
      when reduce_left && has_definition sigma0 P.flags.open_ts env c ->
      report (
        log_eq_spine env "Cons-DeltaL" conv_t t t' (dbg, sigma0) &&=
        unify' ~conv_t env (evar_apprec P.flags.open_ts env sigma0 (get_def_app_stack sigma0 env t)) t')

    (* Unfolding of projections *)
    | _ , Proj (p, c) when reduce_right && stuck != StuckedRight ->
      begin
        let c = RO.whd_all env sigma0 c in (* reduce argument *)
        match
          let (hd, args) = destApp sigma0 c in
          (* Assuming [Proj (p, c)] is well-typed, if [hd] is a constructor,
             it must be of [p]'s record type. *)
          if isConstruct sigma0 hd then args else raise Constr.DestKO
        with
        | args ->
          (* We have found an application of the constructor belonging
            to the record of projection [p].
            (There is no need to check the constructor's index:
            the types guarantee that it is the first and only one)
          *)
          let cont = (args.(Projection.npars p + Projection.arg p), l') in
          report (
            log_eq_spine env "Proj-DeltaR" conv_t t t' (dbg, sigma0) &&=
            unify' ~conv_t env t (evar_apprec P.flags.open_ts env sigma0 cont)
        )
        | exception Constr.DestKO ->
          (* We are stuck on either:
            a) any term
            b) any application
            c) any application of an inductive's constructor
                which is not the constructor of [p]'s type. *)
          report (
            log_eq_spine env "Proj-StuckR" conv_t t t' (dbg, sigma0) &&=
            try_step ~stuck:StuckedRight conv_t env t (mkProj (p, c), l')
          )
      end
    | Proj (p, c), _ when reduce_left && stuck != StuckedLeft ->
      begin
        let c = RO.whd_all env sigma0 c in (* reduce argument *)
        match
          let (hd, args) = destApp sigma0 c in
          (* Assuming [Proj (p, c)] is well-typed, if [hd] is a constructor,
             it must be of [p]'s record type. *)
          if isConstruct sigma0 hd then args else raise Constr.DestKO
        with
        | args ->
          (* We have found an application of the constructor belonging
            to the record of projection [p].
            (There is no need to check the constructor's index:
            the types guarantee that it is the first and only one)
          *)
          let cont = (args.(Projection.npars p + Projection.arg p), l) in
          report (
            log_eq_spine env "Proj-DeltaL" conv_t t t' (dbg, sigma0) &&=
            unify' ~conv_t env (evar_apprec P.flags.open_ts env sigma0 cont) t'
        )
        | exception Constr.DestKO ->
          (* We are stuck on either:
            a) any term
            b) any application
            c) any application of an inductive's constructor
                which is not the constructor of [p]'s type. *)
            report (
              log_eq_spine env "Proj-StuckL" conv_t t t' (dbg, sigma0) &&=
              (* We don't know if we made any progress at all so we make sure to
                 not call [try_step] on the result again by using [unify''] instead of [unify']. *)
              unify''
                ~conv_t
                (fun _ _ _ _  sigma0 dbg -> (dbg, ES.UnifFailure (sigma0, PE.NotSameHead)))
                env
                (mkProj (p, c), l)
                t'
            )
      end
    (* Lam-EtaR *)
    | _, Lambda (name, t1, c1) when reduce_right && CList.is_empty l' && not (isLambda sigma0 c) ->
      report (
        log_eq_spine env "Lam-EtaR" conv_t t t' (dbg, sigma0) &&=
        eta_match conv_t env (name, t1, c1) t)
    (* Lam-EtaL *)
    | Lambda (name, t1, c1), _ when reduce_left && CList.is_empty l && not (isLambda sigma0 c') ->
      report (
        log_eq_spine env "Lam-EtaL" conv_t t t' (dbg, sigma0) &&=
        eta_match conv_t env (name, t1, c1) t')

    | _, _ ->
      (dbg, ES.UnifFailure (sigma0, PE.NotSameHead))

  and is_stuck env sigma (hd, args) =
    let (hd, args) = evar_apprec P.flags.open_ts env sigma (try_unfolding sigma P.flags.open_ts env hd, args) in
    let rec is_unnamed (hd, args) = match kind sigma hd with
      | (Var _|Construct _|Ind _|Const _|Prod _|Sort _|Int _|Float _|Array _) -> false
      | (Case _|Fix _|CoFix _|Meta _|Rel _)-> true
      | Evar _ -> false (* immediate solution without Canon Struct *)
      | Lambda _ -> assert(args = []); true
      | LetIn (_, b, _, c) -> is_unnamed (evar_apprec P.flags.open_ts env sigma (subst1 b c, args))
      | Proj (p, c) -> false
      | App _| Cast _ -> assert false
    in is_unnamed (hd, args)

  and meta_inst dir options conv_t env (ev, subs as evsubs, args) (h, args' as t) sigma dbg =
    if must_inst dir ev && is_variable_subs sigma subs && is_variable_args sigma args then
      begin
        try
          let module P' = (struct
            let flags = P.flags
            let wreduce = Both
            let winst = Both
            let match_evars = P.match_evars
          end : Params) in
          let module U' = (val unif (module P') : Unifier) in
          report (log_eq_spine env "Meta-Inst" conv_t (mkEvar evsubs, args) t (dbg, sigma) &&=
                  let module I' = Inst(U') in
                  I'.instantiate' dir options conv_t env evsubs args t)
        with CannotPrune -> report (dbg, ES.UnifFailure (sigma, PE.NotSameHead))
      end
    else (dbg, ES.UnifFailure (sigma, PE.NotSameHead))

  and meta_deldeps dir options conv_t env (ev, subs as evsubs, args) (h, args' as t) sigma dbg =
    if !options.inst_aggressive && must_inst dir ev then
      begin
        try
	  let (sigma', evsubs', args'') = remove_non_var env sigma evsubs args in
          report (
            log_eq_spine env "Meta-DelDeps" conv_t (mkEvar evsubs, args) t (dbg, sigma') &&=
            switch dir (unify' ~conv_t ~options env) (evsubs', args'') t)
        with CannotPrune -> (dbg, ES.UnifFailure (sigma, PE.NotSameHead))
      end
    else (dbg, ES.UnifFailure (sigma, PE.NotSameHead))

  and meta_specialize dir options conv_t env (ev, subs as evsubs, args) (h, args' as t) sigma dbg =
    if !options.inst_super_aggressive && must_inst dir ev then
      begin
        try
          let (sigma', evsubst', args'') = specialize_evar env sigma evsubs args in
          report (
            log_eq_spine env "Meta-Specialize" conv_t (mkEvar evsubs, args) t (dbg, sigma') &&=
            switch dir (unify' ~conv_t ~options env) (evsubst', args'') t)
        with CannotPrune -> (dbg, ES.UnifFailure (sigma, PE.NotSameHead))
      end
    else (dbg, ES.UnifFailure (sigma, PE.NotSameHead))

  and meta_reduce dir options conv_t env (ev, subs as evsubs, args) (h, args' as t) sigma dbg =
    (* Meta-Reduce: before giving up we see if we can reduce on the right *)
    if must_inst dir ev && ((dir == Original && reduce_right) || (dir == Swap && reduce_left)) then
      if has_definition sigma P.flags.open_ts env h then
        begin
          let t' = evar_apprec P.flags.open_ts env sigma (get_def_app_stack sigma env t) in
          report (
            log_eq_spine env "Meta-Reduce" conv_t (mkEvar evsubs, args) t (dbg, sigma) &&= fun pax ->
            switch dir (unify' ~conv_t ~options env) (mkEvar evsubs, args) t' pax)
        end
      else
        begin
          let t' = evar_apprec P.flags.open_ts env sigma t in
          if not (eq_app_stack sigma t t') then
            begin
              report (
                log_eq_spine env "Meta-Reduce" conv_t (mkEvar evsubs, args) t (dbg, sigma) &&= fun pax ->
                switch dir (unify' ~conv_t ~options env) (mkEvar evsubs, args) t' pax)
            end
          else
            (dbg, ES.UnifFailure (sigma, PE.NotSameHead))
        end
    else
      (dbg, ES.UnifFailure (sigma, PE.NotSameHead))

  and meta_eta dir options conv_t env (ev, subs as evsubs, args) (h, args' as t) sigma dbg =
    (* if the equation is [?f =?= \x.?f x] the occurs check will fail, but there is a solution: eta expansion *)
    if must_inst dir ev && isLambda sigma h && List.length args' = 0 then
      begin
        report (
          log_eq_spine env "Lam-Eta" conv_t (mkEvar evsubs, args) t (dbg, sigma) &&=
          eta_match conv_t ~options env (destLambda sigma h) (mkEvar evsubs, args))
      end
    else
      (dbg, ES.UnifFailure (sigma, PE.NotSameHead))

  (* by invariant, we know that ev is uninstantiated *)
  and instantiate ?(dir=Original) ?(options=default_options) conv_t env
      (_, _ as evsubs) (h, args' as t) (dbg, sigma) =
    meta_inst dir options conv_t env evsubs t sigma dbg
    ||= meta_fo dir options conv_t env evsubs t sigma
    ||= meta_deldeps dir options conv_t env evsubs t sigma
    ||= meta_specialize dir options conv_t env evsubs t sigma
    ||= meta_reduce dir options conv_t env evsubs t sigma
    ||= meta_eta dir options conv_t env evsubs t sigma
    ||= try_solve_simple_eqn options conv_t env evsubs t sigma

  and should_try_fo args (h, args') =
    List.length args > 0 && List.length args' >= List.length args

  (* ?e a1 a2 = h b1 b2 b3 ---> ?e = h b1 /\ a1 = b2 /\ a2 = b3 *)
  and meta_fo dir options conv_t env ((ev, _ as evsubs), args) (h, args' as t) sigma dbg =
    if not (should_try_fo args t) || not (must_inst dir ev) then
      (dbg, ES.UnifFailure (sigma, PE.NotSameHead))
    else
      let (args'1,args'2) =
        CList.chop (List.length args'-List.length args) args' in
      begin report (
          (* Meta-FO *)
          log_eq_spine env "Meta-FO" conv_t (mkEvar evsubs, args)
            t (dbg, sigma) &&= fun (dbg, sigma) ->
            if dir = Original then
              unify' ~conv_t ~options env (mkEvar evsubs, []) (h, args'1) (dbg, sigma) &&=
              ise_list2 (unify_constr env) args args'2
            else
              unify' ~conv_t ~options env (h, args'1) (mkEvar evsubs, []) (dbg, sigma) &&=
              ise_list2 (unify_constr env) args'2 args
        ) end

  (* unifies ty with a product type from {name : a} to some Type *)
  and check_product dbg env sigma ty (name, a) =
    let nc = EConstr.named_context env in
    let naid = Namegen.next_name_away name (Termops.vars_of_env env) in
    let nc' = CND.of_tuple (Context.make_annot naid Sorts.Relevant, None, a) :: nc in
    let sigma', univ = Evd.new_sort_variable Evd.univ_flexible sigma in
    let sigma'',v = Evarutil.new_pure_evar (EConstr.val_of_named_context nc') sigma' (EConstr.mkSort univ) in
    let idsubst = (mkRel 1 :: id_substitution nc) in
    unify_constr ~conv_t:R.CUMUL env ty
      (mkProd (Context.make_annot (Names.Name naid) Sorts.Relevant, a, mkEvar(v, idsubst)))
      (dbg, sigma'')

  and eta_match conv_t ?(options=default_options) env (name, a, t1) (th, tl as t) (dbg, sigma0 ) =
    let env' = EConstr.push_rel (crd_of_tuple (name, None, a)) env in
    let t' = applist (lift 1 th, List.map (lift 1) tl @ [mkRel 1]) in
    let ty = Retyping.get_type_of env sigma0 (applist t) in
    check_product dbg env sigma0 ty (name.binder_name, a) &&=
    unify_constr ~conv_t ~options env' t1 t'

  let instantiate conv_t options env
        (_, _ as evsubs) (h, args' as t) sigma =
    Hashtbl.clear tbl;
    match instantiate ~options conv_t env evsubs t (Logger.init, sigma) with
    | (log, ES.Success sigma) ->
       if get_debug () then
         begin
           Logger.print_latex !latex_file print_eq log;
           Logger.print_to_stdout log;
         end;
       ES.Success sigma
    | (log, ES.UnifFailure (sigma, e)) ->
       if get_debug () then Logger.print_to_stdout log;
       ES.UnifFailure (sigma, e)

end)

let unify_new flags =
  let module P = (struct
    let flags = flags
    let wreduce = Both
    let winst = Both
    let match_evars = None
  end : Params) in
  let module M = (val unif (module P)) in
  M.unify_evar_conv

let unify_evar_conv ts =
  let module P = (struct
    let flags = Evarconv.default_flags_of ts
    let wreduce = Both
    let winst = Both
    let match_evars = None
  end : Params) in
  let module M = (val unif (module P)) in
  M.unify_evar_conv

let unify_match evars ts =
  let module P = (struct
    let flags = Evarconv.default_flags_of ts
    let wreduce = Right
    let winst = Left
    let match_evars = Some evars
  end : Params) in
  let module M = (val unif (module P)) in
  M.unify_evar_conv

let unify_match_nored evars ts =
  let module P = (struct
    let flags = Evarconv.default_flags_of ts
    let wreduce = NoAction
    let winst = Left
    let match_evars = Some evars
  end : Params) in
  let module M = (val unif (module P)) in
  M.unify_evar_conv

let instantiate ?(conv_t=R.CONV) ?(options=default_options) env
      (_, _ as evsubs) t sigma =
  let module P = (struct
    let flags = Evarconv.default_flags_of TransparentState.full
    let wreduce = Both
    let winst = Both
    let match_evars = None
  end : Params) in
  let module M = (val unif (module P)) in
  M.instantiate conv_t options env evsubs (decompose_app sigma t) sigma

let use_munify () = !munify_on
let set_use_munify b =
  if b then try Evarconv.set_evar_conv unify_new with _ -> ();
  munify_on := b

let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optkey = ["Use";"Unicoq"];
  Goptions.optread = use_munify;
  Goptions.optwrite = set_use_munify;
}
