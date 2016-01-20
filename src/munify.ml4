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

DECLARE PLUGIN "munify"

(* $$ *)

(* This should go in its own file, but couldn't figure out
   how to make ocaml to make it part of the plugin :( *)
module Logger = struct

  type 'a nlog =
    Initial
    | Node of 'a * 'a nlog ref * bool * ('a nlog ref) list

  type 'a log = 'a nlog ref

  let state l =
    match !l with
      Initial -> true
    | Node (_, _, s, _) -> s

  let children l =
    match !l with
      Initial -> []
    | Node (_, _, _, c) -> c

  let value l =
    match !l with
      Initial -> []
    | Node (v, _, _, _) -> v

  let parent l =
    match !l with
      Initial -> l
    | Node (_, p, _, _) -> p

  let init = ref Initial

  let is_init l = match !l with Initial -> true | _ -> false

  let currentNode l = !l
  
  let newNode v l =
    let n = ref (Node (v, l, true, [])) in
    match !l with
    | Initial -> n
    | Node (v, p, s, c) -> 
      l := Node (v, p, s, (n::c));
      n
      
  exception DebugException

  let report b l =
    match !l with
    | Initial -> l (* raise DebugException *)
    | Node (v, p, _, c) ->
      l := Node (v, p, b, c);
      if is_init p then l else p

  let reportSuccess = report true

  let reportErr = report false

  let rec pad l = 
    if l <= 0 then () else (Printf.printf "_"; pad (l-1))

  let rec to_parent l =
    match !(parent l) with
    | Initial -> l
    | Node (_, p, _, _) -> to_parent (parent l)

  let rec dump2 i l =
    match !l with
    | Initial -> ()
    | Node ((s, (conv_t, c1, c2)), _, st, ls) ->
      pad i;
      output_string stdout c1;
      output_string stdout " =?= ";
      output_string stdout c2;
      output_string stdout " (";
      output_string stdout s;
      output_string stdout ")";
      if st then
        output_string stdout " OK\n"
      else
        output_string stdout " ERR\n";
      List.iter (dump2 (i+1)) (List.rev ls)

  let dump2 l = dump2 0 (to_parent l)

  let dump s p l =
    let f = open_out_gen [Open_append; Open_creat] 0o666 s in
    let rec dump l =
      match !l with
      | Initial -> ()
      | Node ((s, n), _, true, ls) ->
        output_string f "\fbox{$\inferrule*[left=";
        output_string f s;
        output_string f "]{";
        List.iter (fun l -> dump l; output_string f "\\\\ ") 
          (List.rev ls);
        output_string f "}{";
        p f n;
        output_string f "}$}\n"
      | _ -> ()
    in
    output_string f "\\begin{mathpar}\n";
    dump l;
    output_string f "\\end{mathpar}\n\n";
    flush f;
    close_out f

  let dump s p l = dump s p (to_parent l)
  
end


open Pp
open Term
open Names
open Coqlib
open Universes 
open Globnames
open Vars
open Context
open Errors

(* Getting constrs (primitive Coq terms) from exisiting Coq libraries. *)

let find_constant contrib dir s =
  constr_of_global (Coqlib.find_reference contrib dir s)

let contrib_name = "unicoq"
let init_constant dir s = find_constant contrib_name dir s

let constructors_path = ["Unicoq"]

(* (\* We use lazy as the Coq library is not yet loaded when we *)
(*    initialize the plugin, once [Constructors.Dynamic] is loaded  *)
(*    in the interpreter this will resolve correctly. *\) *)

(* let coq_dynamic_ind = lazy (init_constant constructors_path "dyn") *)
(* let coq_dynamic_constr = lazy (init_constant constructors_path "mkDyn") *)
(* let coq_dynamic_type = lazy (init_constant constructors_path "dyn_type") *)
(* let coq_dynamic_obj = lazy (init_constant constructors_path "dyn_value") *)

(* (\* Reflect the constructor of [dyn] values *\) *)

(* let mkDyn ty value =  *)
(*   mkApp (Lazy.force coq_dynamic_constr, [| ty ; value |]) *)

(* We also need lists from the standard library. *)

let list_path = ["Coq";"Init";"Datatypes"]
let coq_list_ind = lazy (init_constant list_path "list")
let coq_list_nil = lazy (init_constant list_path "nil")
let coq_list_cons = lazy (init_constant list_path "cons")

open Term
open Recordops

let debug = ref false
let munify_on = ref false
let aggressive = ref true
let super_aggressive = ref false
let hash = ref false
let try_solving_eqn = ref false

let set_debug b = 
  debug := b;
  if b then
    begin
      (* Evar instances might depend on Anonymous rels *)
      Detyping.set_detype_anonymous 
        (fun loc n -> Glob_term.GVar (loc, Id.of_string ("_ANONYMOUS_REL_" ^ string_of_int n)))
    end
      
let get_debug () = !debug

let is_aggressive () = !aggressive
let set_aggressive b = aggressive := b

let is_super_aggressive () = !super_aggressive
let set_super_aggressive b = 
  if b then (aggressive := b; super_aggressive := b)
  else super_aggressive := b

let set_hash b = hash := b
let use_hash () = !hash

let set_solving_eqn b = try_solving_eqn := b
let get_solving_eqn () = !try_solving_eqn

let _ = Goptions.declare_bool_option {
  Goptions.optsync  = true;
  Goptions.optdepr  = false;
  Goptions.optname  = "Debugging for unification";
  Goptions.optkey   = ["Unicoq";"Debug"];
  Goptions.optread  = get_debug;
  Goptions.optwrite = set_debug 
}

let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; 
  Goptions.optdepr = false;
  Goptions.optname = "Enable more aggressive prunning";
  Goptions.optkey = ["Unicoq"; "Aggressive"];
  Goptions.optread = is_aggressive;
  Goptions.optwrite = set_aggressive;
}

let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; 
  Goptions.optdepr = false;
  Goptions.optname = 
    "Enable super aggressive prunning, moving arguments applied to a meta-variable" ^
      " to its context (can then be pruned): ?X n -> ?Y[n]. Implies aggressive.";
  Goptions.optkey = ["Unicoq"; "Super"; "Aggressive"];
  Goptions.optread = is_super_aggressive;
  Goptions.optwrite = set_super_aggressive;
}

let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; 
  Goptions.optdepr = false;
  Goptions.optname = "Use a hash table of failures";
  Goptions.optkey = ["Unicoq"; "Use";"Hash"];
  Goptions.optread = use_hash;
  Goptions.optwrite = set_hash;
}

let _ = Goptions.declare_bool_option {
  Goptions.optsync  = true;
  Goptions.optdepr  = false;
  Goptions.optname  = "Try using original algorithm to solve equations ?x = t";
  Goptions.optkey   = ["Unicoq"; "Try"; "Solving";"Eqn"];
  Goptions.optread  = get_solving_eqn;
  Goptions.optwrite = set_solving_eqn 
}


let stat_unif_problems = ref Big_int.zero_big_int
let stat_minst = ref Big_int.zero_big_int

VERNAC COMMAND EXTEND PrintMunifyStats CLASSIFIED AS SIDEFF
  | [ "Print" "Unicoq" "Stats" ] -> [
    Printf.printf "STATS:\t%s\t\t%s\n" 
      (Big_int.string_of_big_int !stat_unif_problems) 
      (Big_int.string_of_big_int !stat_minst)
  ]
END

(** Not in 8.5 *)
(* Note: let-in contributes to the instance *)
let make_evar_instance sign args =
  let rec instrec = function
    | (id,_,_) :: sign, c::args when isVarId id c -> instrec (sign,args)
    | (id,_,_) :: sign, c::args -> (id,c) :: instrec (sign,args)
    | [],[] -> []
    | [],_ | _,[] -> anomaly (str"Signature and its instance do not match")
  in
    instrec (sign,args)

let instantiate_evar sign c args =
  let inst = make_evar_instance sign args in
  if inst = [] then c else replace_vars inst c
(** Not in 8.5 *)

type 'a unif = 
    Success of 'a Logger.log * Evd.evar_map 
  | Err of 'a Logger.log

let success (l,v) = 
  let l = Logger.reportSuccess l in
  Success (l,v)

let err l = 
  let l = Logger.reportErr l in
  Err l

let report s =
  match s with 
  | Success (l, v) -> success (l, v)
  | Err l -> err l

let (>>=) opt f = 
  match opt with
  | Some(x) -> f x
  | None -> None
   
let return x = Some x

let (&&=) opt f = 
  match opt with
  | Success (l, x) -> f (l, x)
  | _ -> opt
    

let (||=) opt f = 
  match opt with
  | Err l -> f l
  | _ -> opt


let latexify s =
  let s = Str.global_replace (Str.regexp "\\\\") "\\\\\\\\" s in
  let s = Str.global_replace (Str.regexp "{") "\{" s in
  let s = Str.global_replace (Str.regexp "}") "\}" s in
  let s = Str.global_replace (Str.regexp "%") "\\%" s in
  let s = Str.global_replace (Str.regexp "#") "\\#" s in
  Str.global_replace (Str.regexp "~") "\\~" s
  
let log_eq env rule conv_t t1 t2 (l, sigma) = 
  if not (get_debug ()) then
    Success (l, sigma)
  else
    let str1 = Pp.string_of_ppcmds (Termops.print_constr_env env t1) in
    let str2 = Pp.string_of_ppcmds (Termops.print_constr_env env t2) in 
    let str1 = latexify str1 in
    let str2 = latexify str2 in
    let l = Logger.newNode (rule, (conv_t, str1, str2)) l in 
    Success (l, sigma)
  
let log_eq_spine env rule conv_t t1 t2 = 
  log_eq env rule conv_t (applist t1) (applist t2)


let is_success s = match s with Success _ -> true | _ -> false


let ise_list2 f l1 l2 =
  let rec ise_list2 l1 l2 (l, evd) =
    match l1,l2 with
      [], [] -> Success (l, evd)
    | x::l1, y::l2 ->
      f x y (l, evd) &&= ise_list2 l1 l2
    | _ -> Err l in
  ise_list2 l1 l2

let ise_array2 f v1 v2 evd =
  let l1 = Array.length v1 in
  let l2 = Array.length v2 in
  assert (l1 <= l2) ;
  let diff = l2 - l1 in
  let rec allrec n (l, evdi) = 
    if n >= l1 then Success (l, evdi)
    else
      f v1.(n) v2.(n+diff) (l, evdi) &&=
      allrec (n+1)
  in
  allrec 0 evd


let id_substitution nc = 
  let s = fold_named_context (fun (n,_,_) s -> mkVar n :: s) nc ~init:[] in
  Array.of_list s

(* pre: isVar v1 *)
let is_same_var v1 v2 =  isVar v2 && (destVar v1 = destVar v2)

(* pre: isRel v1 *)
let is_same_rel v1 v2 = isRel v2 && destRel v1 = destRel v2

let is_same_evar i1 ev2 =
  match kind_of_term ev2 with
  | Evar (i2, _) -> i1 = i2
  | _ -> false

let isVarOrRel c = isVar c || isRel c

let is_variable_subs = CArray.for_all (fun c -> isVar c || isRel c)

let is_variable_args = List.for_all (fun c -> isVar c || isRel c)    

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

let find_unique_var = find_unique isVar destVar

let find_unique_rel = find_unique isRel destRel


let has_definition ts env t = 
  if isVar t then
    let var = destVar t in
    if not (Closure.is_transparent_variable ts var) then 
      false
    else
      let (_, v,_) = Environ.lookup_named var env in
      match v with
	| Some _ -> true
	| _ -> false
  else if isRel t then
    let n = destRel t in
    let (_,v,_) = Environ.lookup_rel n env in
    match v with
      | Some _ -> true
      | _ -> false
  else if isConst t then
    let c,_ = destConst t in
      Closure.is_transparent_constant ts c && 
      Environ.evaluable_constant c env
  else
    false

let get_definition env t =
  if isVar t then
    let var = destVar t in
    let (_, v,_) = Environ.lookup_named var env in
    match v with
      | Some c -> c
      | _ -> anomaly (str"get_definition for var didn't have definition!")
  else if isRel t then
    let n = destRel t in
    let (_,v,_) = Environ.lookup_rel n env in 
    match v with
      | Some v -> (lift n) v
      | _ -> anomaly (str"get_definition for rel didn't have definition!")
  else if isConst t then
    let c = destConst t in
    Environ.constant_value_in env c
  else
    anomaly (str"get_definition didn't have definition!")

let get_def_app_stack env (c, args) =
  let (d, dargs) = decompose_app (get_definition env c) in
  (d, dargs @ args)

let try_unfolding ts env t =
  if has_definition ts env t then
    get_definition env t
  else
    t


let (-.) n m =
  if n > m then n - m
  else 0

(* pre: |ctx| = |subs| and subs and args are both a list of vars or rels.
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
   Prunning is needed to avoid failing when there is hope: the unification 
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
let invert map sigma ctx t subs args ev' = 
  let sargs = subs @ args in
  let in_subs j = j < List.length ctx in
  let rmap = ref map in
  let rec invert' inside_evar t i =
    let t = Evarutil.whd_head_evar sigma t in
    match kind_of_term t with
      | Var id -> 
	find_unique_var id sargs >>= fun j -> 
	if in_subs j then
	  let (name, _, _) = List.nth ctx j in
	  return (mkVar name)
	else
	  return (mkRel (List.length sargs - j + i))
      | Rel j when j > i-> 
	find_unique_rel (j-i) sargs >>= fun k -> 
	if in_subs k then
	  let (name, _, _) = List.nth ctx k in
	  return (mkVar name)
	else
	  return (mkRel (List.length sargs - k + i))

      | Evar (ev, evargs) when Evar.equal ev ev' ->
        None

      | Evar (ev, evargs) ->
	begin
	  let f (j : int) c  = 
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
	  try return (mkEvar (ev, Array.mapi f evargs))
	  with Exit -> None
	end
      | _ -> 
	try return (map_constr_with_binders succ (fun i c -> 
	  match invert' inside_evar c i with
	    | Some c' -> c'
	    | None -> raise Exit) i t)
	with Exit -> None
  in
  (try invert' false t 0 with NotUnique -> None) >>= fun c' ->
  return (!rmap, c')

let collect_vars =
  let rec aux vars c = match kind_of_term c with
  | Var id -> Names.Idset.add id vars
  | _ -> fold_constr aux vars c in
  aux Names.Idset.empty

let free_vars_intersect tm vars = 
  Names.Idset.exists (fun v -> List.mem v vars) (collect_vars tm)

let some_or_prop o =
  match o with
      None -> mkProp
    | Some tm -> tm

(** removes the positions in the list, and all dependent elements *)
let remove l pos =
  let length = List.length l in
  let l = List.rev l in
  let rec remove' i l vs =
    match l with
      | [] -> []
      | ((x, o, t as p) :: s) -> 
        if List.mem i pos 
	  || free_vars_intersect t vs 
	  || free_vars_intersect (some_or_prop o) vs then
          remove' (i-1) s (x :: vs)
        else
          (p :: remove' (i-1) s vs)
  in List.rev (remove' (length-1) l [])

let free_vars_in tm vars = 
  Names.Idset.for_all (fun v -> List.mem v vars) (collect_vars tm)

exception CannotPrune

(** ev is the evar and plist the indices to prune.  from ?ev : T[env]
    it creates a new evar ?ev' with a shorter context env' such that
    ?ev := ?ev'[id_env']. If the prunning is unsuccessful, it throws
    the exception CannotPrune. *)
let rec prune evd (ev, plist) =
  (* HACK: assume that if ev is defined, then it was already prunned *)
  if Evd.is_defined evd ev then evd
  else
  let evi = Evd.find_undefined evd ev in
  let env = Evd.evar_filtered_context evi in
  let env' = remove env plist in
  let env_val' = (List.fold_right Environ.push_named_context_val env' 
                    Environ.empty_named_context_val) in
  (* the type of the evar may contain an evar depending on the some of
     the vars that we want to prune, so we need to prune that
     aswell *)
  let concl = Reductionops.nf_evar evd (Evd.evar_concl evi) in
  let id_env' = Array.to_list (id_substitution env') in
  match invert Evar.Map.empty evd env' concl id_env' [] ev with
      None -> raise CannotPrune
    | Some (m, concl) ->
      let evd = prune_all m evd in
      let concl = Reductionops.nf_evar evd (Evd.evar_concl evi) in
      let evd', ev' = Evarutil.new_evar_instance env_val' evd 
	concl id_env' in
      Evd.define ev ev' evd'

and prune_all map evd =
  List.fold_left prune evd (Evar.Map.bindings map)

(* pre: |s1| = |s2| 
   pos: None if s1 or s2 are not equal and not var to var subs
        Some l with l list of indexes where s1 and s2 do not agree *)
let intersect env sigma s1 s2 =
  let n = Array.length s1 in
  let rec intsct i =
    if i < n then
      intsct (i+1) >>= fun l ->
      if eq_constr s1.(i) s2.(i) then
        Some l
      else
        if (isVar s1.(i) || isRel s1.(i)) &&  (isVar s2.(i) || isRel s2.(i)) then
          Some (i :: l) (* both position holds variables: they are indeed different *)
        else if is_aggressive () then Some (i :: l)
	else None
    else Some []
  in 
  assert (Array.length s2 = n) ;
  intsct 0

(* pre: ev is a not-defined evar *)
let unify_same dbg env sigma ev subs1 subs2 =
  match intersect env sigma subs1 subs2 with
  | Some [] -> (false, Success (dbg, sigma))
  | Some l -> begin
              try 
		(true, Success (dbg, prune sigma (ev, l)))
              with CannotPrune -> (false, Err dbg)
              end
  | _ -> (false, Err dbg)



(* given a list of arguments [args] = [x1 .. xn], a [body] with free
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
    return (ars, mkLambda (Namegen.named_hd env ty Anonymous, ty, bdy))) args (return (args, body)) 
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

let check_conv_record (t1,l1) (t2,l2) =
  try
    let proji = Globnames.global_of_constr t1 in
    let canon_s,l2_effective =
      try
	match kind_of_term t2 with
	    Prod (_,a,b) -> (* assert (l2=[]); *)
      	      if Termops.dependent (mkRel 1) b then raise Not_found
	      else lookup_canonical_conversion (proji, Prod_cs),[a;Termops.pop b]
	  | Sort s ->
	      lookup_canonical_conversion
		(proji, Sort_cs (family_of_sort s)),[]
	  | _ ->
	      let c2 = Globnames.global_of_constr t2 in
		Recordops.lookup_canonical_conversion (proji, Const_cs c2),l2
      with Not_found ->
	lookup_canonical_conversion (proji, Default_cs),[]
    in
    let t, { o_DEF = c; o_INJ=n; o_TABS = bs;
          o_TPARAMS = params; o_NPARAMS = nparams; o_TCOMPS = us } = canon_s in
    let params1, c1, extra_args1 =
      match CList.chop nparams l1 with
	| params1, c1::extra_args1 -> params1, c1, extra_args1
	| _ -> raise Not_found in
    let us2,extra_args2 = CList.chop (List.length us) l2_effective in
    c,bs,(params,params1),(us,us2),(extra_args1,extra_args2),c1,
    (n,applist(t2,l2))
  with Failure _ | Not_found ->
    raise ProjectionNotFound

let run_function = ref (fun _ _ _ -> None)
let set_run f = run_function := f

let lift_constr = ref (lazy mkProp)
let set_lift_constr c = lift_constr := c

let is_lift c = 
  try eq_constr c (Lazy.force !lift_constr)
  with Not_found -> false


let rec pad l = if l <= 0 then () else (Printf.printf "_"; pad (l-1))

let print_bar l = if l > 0 then Printf.printf "%s" "|" else ()
    
let debug_str s l =
  if !debug then 
    begin
      print_bar l;
      pad l;
      Printf.printf "%s\n" s
    end
  else
    ()

let debug_eq sigma env t c1 c2 l = 
  print_bar l;
  pad l;
  Pp.msg (Termops.print_constr_env env (Evarutil.nf_evar sigma (applist c1)));
  Printf.printf "%s" (if t == Reduction.CONV then " =?= " else " <?= ");
  Pp.msg (Termops.print_constr_env env (Evarutil.nf_evar sigma (applist c2)));
  Printf.printf "\n" 
 
let print_eq f (conv_t, c1, c2) = 
  output_string f "\\lstinline{";
  output_string f c1;
  output_string f "}~\approx_{";
  output_string f (if conv_t == Reduction.CONV then "=" else "\leq");
  output_string f "}~\\lstinline{";
  output_string f c2;
  output_string f "}"

type stucked = NotStucked | StuckedLeft | StuckedRight
type direction = Original | Swap

let evar_apprec ts env sigma (c, stack) =
  let rec aux s =
    let ((t,stack),cststack) =
      Reductionops.(whd_betaiota_deltazeta_for_iota_state 
        ts env sigma Cst_stack.empty s)
    in
    match kind_of_term t with
      | Evar (evk,_ as ev) when Evd.is_defined sigma evk ->
	  aux (Evd.existential_value sigma ev, stack)
      | _ -> 
	match Reductionops.Stack.list_of_app_stack stack with
	| None -> decompose_app (Reductionops.Stack.zip (t, stack))
	| Some stack -> (t, stack)
  in aux (c, Reductionops.Stack.append_app_list stack Reductionops.Stack.empty)

let eq_app_stack (c, l) (c', l') = 
  Term.eq_constr c c' && List.for_all2 Term.eq_constr l l'

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

let remove_non_var env sigma (ev, subs as evsubs) args =
  let length = Array.length subs in
  let (_, ps) = Array.fold_right (fun a (i, s) -> 
    if isVarOrRel a && not (array_mem_to_i a i subs || List.mem a args) then (i-1,s)
    else (i-1, i::s)) subs (length-1, [])  in
  if ps = [] then raise CannotPrune
  else
    let sigma' = prune sigma (ev, ps) in
    (sigma', Reductionops.nf_evar sigma' (mkEvar evsubs), args)


let specialize_evar env sigma (ev, subs) args =
  match args with
  | [] -> raise CannotPrune
  | hd :: tl ->
    let sigma', lam = Evarutil.define_evar_as_lambda env sigma (ev, subs) in
    let (n, dom, codom) = destLambda (Evarutil.nf_evar sigma' lam) in
      sigma', subst1 hd codom, tl

exception InternalException

let tbl = Hashtbl.create 1000

let tblfind t x = try Hashtbl.find t x with Not_found -> false
  
let switch dir f t u = if dir == Original then f t u else f u t


(* pre: c and c' are in whdnf with our definition of whd *)
let rec unify' ?(conv_t=Reduction.CONV) ts env (c, l) (c', l') (dbg, sigma0) : 'a unif =
  let (c, l1) = decompose_app (Evarutil.whd_head_evar sigma0 c) in
  let (c', l2) = decompose_app (Evarutil.whd_head_evar sigma0 c') in
  let l, l' = l1 @ l, l2 @ l' in
  let t, t' = (c, l), (c', l') in
    let res =
      let sigma1, b = 
	let appt = applist t and appt' = applist t' in
	let ground =
	  Evarutil.(is_ground_term sigma0 appt && is_ground_term sigma0 appt')
	in 
	  if ground then 
	    try Reductionops.infer_conv ~pb:conv_t ~ts env sigma0 appt appt' 
	    with Univ.UniverseInconsistency _ -> sigma0, false
	  else sigma0, false
      in
      if b then
        report (log_eq_spine env "Reduce-Same" conv_t t t' (dbg, sigma1))
      else if use_hash () && tblfind tbl (sigma0, env, (c,l),(c',l')) then begin
        log_eq_spine env "Hash-Hit" conv_t t t' (dbg, sigma0) &&= fun (dbg, _) ->
	  report (Err dbg)
      end 
      else begin
	    match (kind_of_term c, kind_of_term c') with
	    | Evar _, _ 
	    | _, Evar _ ->
	      one_is_meta dbg ts conv_t env sigma0 t t'

	    | _, _  ->
	      (
		if (isConst c || isConst c') && not (eq_constr c c') then
		  begin
		    if is_lift c && List.length l = 3 then
		      run_and_unify dbg ts env sigma0 l t'
		    else if is_lift c' && List.length l' = 3 then
		      run_and_unify dbg ts env sigma0 l' t
		    else
		      Err dbg
		  end
		else
		  Err dbg
	      ) ||= fun dbg ->
		(
		  if (isConst c || isConst c') && not (eq_constr c c') then
		    try conv_record dbg ts env sigma0 t t'
		    with ProjectionNotFound ->
		      try conv_record dbg ts env sigma0 t' t
		      with ProjectionNotFound -> Err dbg
		  else
		    Err dbg
		) ||= fun dbg ->
		  (
		    let n = List.length l in
		    let m = List.length l' in
		      if n = m then 
			begin report (
       log_eq_spine env "App-FO" conv_t t t' (dbg, sigma0) &&=
       compare_heads conv_t ts env c c' &&=
       ise_list2 (unify_constr ts env) l l' 
     ) end
		      else
			Err dbg
		  ) ||= fun dbg ->
		    (
		      try_step dbg conv_t ts env sigma0 t t'
		    ) 
	  end
    in
    if not (is_success res) && use_hash () then
      Hashtbl.add tbl (sigma0, env, (c, l), (c',l')) true 
    else ();
    res

and unify_constr ?(conv_t=Reduction.CONV) ts env t t' : 'b -> 'a unif =
  unify' ~conv_t ts env (decompose_app t) (decompose_app t')

and run_and_unify dbg ts env sigma0 args ty : 'a unif =
  let a, f, v = List.nth args 0, List.nth args 1, List.nth args 2 in
    unify' ~conv_t:Reduction.CUMUL ts env (decompose_app a) ty (dbg, sigma0) &&= fun (dbg, sigma1) ->
      match !run_function env sigma1 f with
      | Some (sigma2, v') -> unify' ts env (decompose_app v) (decompose_app v') (dbg, sigma2)
      | _ -> Err dbg

and try_solve_simple_eqn ?(dir=Original) ts conv_t env evsubs args t sigma dbg : 'a unif =
  if get_solving_eqn () then 
    try
      let t = Evarsolve.solve_pattern_eqn env args (applist t) in
      let pbty = match conv_t with 
	| Reduction.CONV -> None
	| Reduction.CUMUL -> Some (dir == Original)
      in
	match Evarsolve.solve_simple_eqn (unify_evar_conv ts) env sigma (pbty, evsubs, t) with
	| Evarsolve.Success sigma' ->
	  Printf.printf "%s" "solve_simple_eqn solved it: ";
	  debug_eq sigma env Reduction.CONV (mkEvar evsubs, []) (decompose_app t) 0;
	  Success (dbg, sigma')
	| Evarsolve.UnifFailure (sigma', error) -> Err dbg
    with _ -> 
      Printf.printf "%s" "solve_simple_eqn failed!";
      Err dbg
  else
    Err dbg

and one_is_meta dbg ts conv_t env sigma0 (c, l as t) (c', l' as t') =
  (* first we instantiate all defined metas *)
  let nf_map = List.map (fun a->Reductionops.nf_evar sigma0 a) in
  let (c, l) = (Reductionops.nf_evar sigma0 c, nf_map l) in 
  let (c', l') = (Reductionops.nf_evar sigma0 c', nf_map l') in
  if isEvar c && isEvar c' then
    let (k1, s1 as e1), (k2, s2 as e2) = destEvar c, destEvar c' in
    if k1 = k2 then
      (* Meta-Same *)
      begin
        let (b,p) = unify_same dbg env sigma0 k1 s1 s2 in
        let dbg, sigma = match p with
          | Success (dbg, sigma) -> dbg, sigma
          | Err dbg -> dbg, sigma0
        in
        log_eq_spine env (if b then "Meta-Same" else "Meta-Same-Same") conv_t t t' (dbg, sigma) &&= fun dbg, sigma ->
        if is_success p then
          report (ise_list2 (unify_constr ts env) l l' (dbg, sigma))
        else
          report (Err dbg)
      end
    else
      begin
	(* Meta-Meta *)
        if k1 > k2 then
          instantiate ts conv_t env e1 l t' sigma0 dbg
          ||= instantiate ~dir:Swap ts conv_t env e2 l' t sigma0
          ||= try_solve_simple_eqn ts conv_t env e1 l t' sigma0
        else
          instantiate ~dir:Swap ts conv_t env e2 l' t sigma0 dbg
          ||= instantiate ts conv_t env e1 l t' sigma0
          ||= try_solve_simple_eqn ~dir:Swap ts conv_t env e2 l' t sigma0
      end
  else
  if isEvar c then
    if is_lift c' && List.length l' = 3 then
      run_and_unify dbg ts env sigma0 l' t
    else
      begin
	let e1 = destEvar c in
        instantiate ts conv_t env e1 l t' sigma0 dbg
        ||= try_solve_simple_eqn ts conv_t env e1 l t' sigma0
      end
  else
  if is_lift c && List.length l = 3 then
    run_and_unify dbg ts env sigma0 l t'
  else
    begin
      let e2 = destEvar c' in
      instantiate ~dir:Swap ts conv_t env e2 l' t sigma0 dbg
      ||= try_solve_simple_eqn ~dir:Swap ts conv_t env e2 l' t sigma0
    end

and compare_heads conv_t ts env c c' (dbg, sigma0) =
  let rigid_same () = report (log_eq env "Rigid-Same" conv_t c c' (dbg, sigma0)) in
  match (kind_of_term c, kind_of_term c') with
  (* Type-Same *)
  | Sort s1, Sort s2 ->
    log_eq env "Type-Same" conv_t c c' (dbg, sigma0) &&= fun (dbg, sigma0) ->
    begin
      try
	let sigma1 = match conv_t with
	  | Reduction.CONV -> Evd.set_eq_sort env sigma0 s1 s2 
	  | Reduction.CUMUL -> Evd.set_leq_sort env sigma0 s1 s2
        in
        report (Success (dbg, sigma1))
      with Univ.UniverseInconsistency e -> 
	debug_str (Printf.sprintf "Type-Same exception: %s"
		     (Pp.string_of_ppcmds (Univ.explain_universe_inconsistency Univ.Level.pr e))) 0;
	report (Err dbg)
    end

  (* Lam-Same *)
  | Lambda (name, t1, c1), Lambda (_, t2, c2) ->
    let env' = Environ.push_rel (name, None, t1) env in
    report (
      log_eq env "Lam-Same" conv_t c c' (dbg, sigma0) &&=
      unify_constr ts env t1 t2 &&= 
      unify_constr ~conv_t ts env' c1 c2)
    
  (* Prod-Same *)
  | Prod (name, t1, c1), Prod (_, t2, c2) ->
    report (
      log_eq env "Prod-Same" conv_t c c' (dbg, sigma0) &&=
      unify_constr ts env t1 t2 &&=
      unify_constr ~conv_t ts (Environ.push_rel (name,None,t1) env) c1 c2)

  | LetIn (name, trm1, ty1, body1), LetIn (_, trm2, ty2, body2) ->
    (* Let-Same *)
    let env' = Environ.push_rel (name, Some trm1, ty1) env in
    report (
      log_eq env "Let-Same" conv_t c c' (dbg, sigma0) &&=
      unify_constr ts env ty1 ty2 &&=
      unify_constr ts env trm1 trm2 &&=
      unify_constr ~conv_t ts env' body1 body2)
          
  (* Rigid-Same *)
  | Rel n1, Rel n2 when n1 = n2 ->
    rigid_same ()
  | Var id1, Var id2 when Id.equal id1 id2 ->
    rigid_same ()
  | Const c1, Const c2 when Univ.eq_puniverses Names.eq_constant c1 c2 ->
    rigid_same ()
  | Ind c1, Ind c2 when Univ.eq_puniverses Names.eq_ind c1 c2 ->
    rigid_same ()
  | Construct c1, Construct c2 
    when Univ.eq_puniverses Names.eq_constructor c1 c2  ->
    rigid_same ()

  | CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2))
    when i1 = i2 ->
    report (
      log_eq env "CoFix-Same" conv_t c c' (dbg, sigma0) &&=
      ise_array2 (unify_constr ts env) tys1 tys2 &&=
      ise_array2 (unify_constr ts (Environ.push_rec_types recdef1 env)) bds1 bds2)

  | Case (_, p1, c1, cl1), Case (_, p2, c2, cl2) ->
    report (
      log_eq env "Case-Same" conv_t c c' (dbg, sigma0) &&=
      unify_constr ts env p1 p2 &&=
      unify_constr ts env c1 c2 &&=
      ise_array2 (unify_constr ts env) cl1 cl2)

  | Fix (li1, (_, tys1, bds1 as recdef1)), Fix (li2, (_, tys2, bds2)) 
    when li1 = li2 ->
    report (
      log_eq env "Fix-Same" conv_t c c' (dbg, sigma0) &&=
      ise_array2 (unify_constr ts env) tys1 tys2 &&=
      ise_array2 (unify_constr ts (Environ.push_rec_types recdef1 env)) bds1 bds2)

  | _, _ -> Err dbg

and is_reducible ts env (c, l) =
  (isLambda c && l <> []) ||
    (isLetIn c) ||
    ((isRel c || isVar c) && has_definition ts env c)

and try_step ?(stuck=NotStucked) dbg conv_t ts env sigma0 (c, l as t) (c', l' as t') =
  match (kind_of_term c, kind_of_term c') with
  (* Lam-BetaR *)
  | _, Lambda (_, _, trm) when not (CList.is_empty l') ->
    let t2 = (subst1 (List.hd l') trm, List.tl l') in
    report (
      log_eq_spine env "Lam-BetaR" conv_t t t' (dbg, sigma0) &&=
      unify' ~conv_t ts env t t2)

  | _, LetIn (_, trm, _, body) ->
    let t2 = (subst1 trm body, l') in
    report (
      log_eq_spine env "Let-ZetaR" conv_t t t' (dbg, sigma0) &&=
      unify' ~conv_t ts env t t2)

  | _, Case _ | _, Fix _ when stuck != StuckedRight ->
    let t2 = evar_apprec ts env sigma0 t' in
      if not (eq_app_stack t' t2) then
        begin report (
          log_eq_spine env "Case-IotaR" conv_t t t' (dbg, sigma0) &&=
	  unify' ~conv_t ts env t t2)
	end
      else if stuck = NotStucked then
	try_step ~stuck:StuckedRight dbg conv_t ts env sigma0 t t'
      else Err dbg

  (* Lam-BetaL *)
  | Lambda (_, _, trm), _ when not (CList.is_empty l) ->
    let t1 = (subst1 (List.hd l) trm, List.tl l) in
    report (
      log_eq_spine env "Lam-BetaL" conv_t t t' (dbg, sigma0) &&=
      unify' ~conv_t ts env t1 t')
  (* Let-ZetaL *)
  | LetIn (_, trm, _, body), _ ->
    let t1 = (subst1 trm body, l) in
    report (
      log_eq_spine env "Let-ZetaL" conv_t t t' (dbg, sigma0) &&=
      unify' ~conv_t ts env t1 t')

  | Case _, _ | Fix _, _ when stuck != StuckedLeft ->
    let t2 = evar_apprec ts env sigma0 t in
      if not (eq_app_stack t t2) then
	begin report (
          log_eq_spine env "Case-IotaL" conv_t t t' (dbg, sigma0) &&=
	  unify' ~conv_t ts env t2 t')
	end
      else if stuck == NotStucked then
	try_step ~stuck:StuckedLeft dbg conv_t ts env sigma0 t t'
      else Err dbg

  (* Constants get unfolded after everything else *)
  | _, Const _
  | _, Rel _
  | _, Var _ when has_definition ts env c' && stuck == NotStucked ->
    if is_stuck ts env sigma0 t' then
      try_step ~stuck:StuckedRight dbg conv_t ts env sigma0 t t'
    else report (
      log_eq_spine env "Cons-DeltaNotStuckR" conv_t t t' (dbg, sigma0) &&=
      unify' ~conv_t ts env t (evar_apprec ts env sigma0 (get_def_app_stack env t')))
  | Const _, _ 
  | Rel _, _ 
  | Var _, _  when has_definition ts env c && stuck == StuckedRight ->
    report (
      log_eq_spine env "Cons-DeltaStuckL" conv_t t t'  (dbg, sigma0) &&=
      unify' ~conv_t ts env (evar_apprec ts env sigma0 (get_def_app_stack env t)) t')

  | _, Const _ 
  | _, Rel _
  | _, Var _ when has_definition ts env c' ->
    report (
      log_eq_spine env "Cons-DeltaR" conv_t t t' (dbg, sigma0) &&=
      unify' ~conv_t ts env t (evar_apprec ts env sigma0 (get_def_app_stack env t')))
  | Const _, _
  | Rel _, _ 
  | Var _, _  when has_definition ts env c ->
    report (
      log_eq_spine env "Cons-DeltaL" conv_t t t' (dbg, sigma0) &&=
      unify' ~conv_t ts env (evar_apprec ts env sigma0 (get_def_app_stack env t)) t')

  (* Lam-EtaR *)
  | _, Lambda (name, t1, c1) when CList.is_empty l' && not (isLambda c) ->
    report (
      log_eq_spine env "Lam-EtaR" conv_t t t' (dbg, sigma0) &&= 
      eta_match conv_t ts env (name, t1, c1) t)
  (* Lam-EtaL *)
  | Lambda (name, t1, c1), _ when CList.is_empty l && not (isLambda c') ->
    report (
      log_eq_spine env "Lam-EtaL" conv_t t t' (dbg, sigma0) &&=
      eta_match conv_t ts env (name, t1, c1) t')

  | _, _ -> Err dbg

and is_stuck ts env sigma (hd, args) =
  let (hd, args) = evar_apprec ts env sigma (try_unfolding ts env hd, args) in
  let rec is_unnamed (hd, args) = match kind_of_term hd with
    | (Var _|Construct _|Ind _|Const _|Prod _|Sort _) -> false
    | (Case _|Fix _|CoFix _|Meta _|Rel _)-> true
    | Evar _ -> false (* immediate solution without Canon Struct *)
    | Lambda _ -> assert(args = []); true
    | LetIn (_, b, _, c) -> is_unnamed (evar_apprec ts env sigma (subst1 b c, args))
    | Proj (p, c) -> false
    | App _| Cast _ -> assert false
  in is_unnamed (hd, args)
    
and remove_equal_tail (h, args) (h', args') =
  let rargs = List.rev args in
  let rargs' = List.rev args' in
  let noccur i xs ys =
    not (Termops.occur_term i h')
    && not (Termops.occur_term i h)
    && not (List.exists (Termops.occur_term i) ys)
    && not (List.exists (Termops.occur_term i) xs) in
  let rec remove rargs rargs' =
    match rargs, rargs' with
    | (x :: xs), (y :: ys) when eq_constr x y && noccur x xs ys -> remove xs ys
    | _, _ -> rargs, rargs'
  in 
  let (xs, ys) = remove rargs rargs' in
    (List.rev xs, List.rev ys)

(* pre: args and args' are lists of vars and/or rels. subs is an array of rels and vars. *) 
and instantiate' ts dir conv_t env (ev, subs as uv) args (h, args') (dbg, sigma0) =
  let args, args' = remove_equal_tail (mkEvar uv, args) (h, args') in
  (* beta-reduce to remove dependencies *)
  let t = Reductionops.whd_beta sigma0 (applist (h, args')) in 
  let evi = Evd.find_undefined sigma0 ev in
  let nc = Evd.evar_filtered_context evi in
  let res = 
    let subsl = Array.to_list subs in
      invert Evar.Map.empty sigma0 nc t subsl args ev >>= fun (map, t') ->
      fill_lambdas_invert_types map env sigma0 nc t' subsl args ev >>= fun (map, t') ->
        let sigma1 = prune_all map sigma0 in
	let t' = Evarutil.nf_evar sigma1 t' in
	let sigma1, t' = 
	  Evarsolve.refresh_universes
	    (if conv_t == Reduction.CUMUL && isArity t' then
	      (* ?X <= Type(i) -> X := Type j, j <= i *)
	      (* Type(i) <= X -> X := Type j, i <= j *)
	      Some (dir == Original) 
	   else None)
	    (Environ.push_named_context nc env) sigma1 t' in
	let t'' = instantiate_evar nc t' subsl in
	let ty = Evd.existential_type sigma1 uv in
	let unifty = 
	  try 
	    match kind_of_term t'' with
	    | Evar (evk2, _) ->
              (* ?X : Π Δ. Type i = ?Y : Π Δ'. Type j.
		 The body of ?X and ?Y just has to be of type Π Δ. Type k for some k <= i, j. *)
	      let evienv = Evd.evar_env evi in
	      let ctx1, i = Reduction.dest_arity evienv evi.Evd.evar_concl in
	      let evi2 = Evd.find sigma1 evk2 in
	      let evi2env = Evd.evar_env evi2 in
	      let ctx2, j = Reduction.dest_arity evi2env evi2.Evd.evar_concl in
	      let ui, uj = univ_of_sort i, univ_of_sort j in
		if i == j || Evd.check_eq sigma1 ui uj
		then (* Shortcut, i = j *) 
		  Success (dbg, sigma1)
		else if Evd.check_leq sigma1 ui uj then
		  let t2 = it_mkProd_or_LetIn (mkSort i) ctx2 in
		    Success (dbg, Evd.downcast evk2 t2 sigma1)
		else if Evd.check_leq sigma1 uj ui then
		  let t1 = it_mkProd_or_LetIn (mkSort j) ctx1 in
		    Success (dbg, Evd.downcast ev t1 sigma1)
		else
		  let sigma1, k = Evd.new_sort_variable Evd.univ_flexible_alg sigma1 in
		  let t1 = it_mkProd_or_LetIn (mkSort k) ctx1 in
		  let t2 = it_mkProd_or_LetIn (mkSort k) ctx2 in
		  let sigma1 = Evd.set_leq_sort env (Evd.set_leq_sort env sigma1 k i) k j in
		    Success (dbg, Evd.downcast evk2 t2 (Evd.downcast ev t1 sigma1))
	    | _ -> raise Reduction.NotArity
	  with Reduction.NotArity -> 
	    let ty' = Retyping.get_type_of env sigma1 t'' in
	      unify_constr ~conv_t:Reduction.CUMUL ts env ty' ty (dbg, sigma1) 
	in
	let p = unifty &&= fun (dbg, sigma2) ->
	  let t' = Reductionops.nf_evar sigma2 t' in
	    if Termops.occur_meta t' || Termops.occur_evar ev t' then 
	      Err dbg
	    else
	      (stat_minst := Big_int.succ_big_int !stat_minst;
	       Success (dbg, Evd.define ev t' sigma2))
	in
	  Some p
  in
    match res with
    | Some r -> r
    | None -> Err dbg
    
and meta_inst dir ts conv_t env (ev, subs as evsubs) args (h, args' as t) sigma dbg =
    if is_variable_subs subs && is_variable_args args then
      begin
        try 
          report (log_eq_spine env "Meta-Inst" conv_t (mkEvar evsubs, args) t (dbg, sigma) &&=
                  instantiate' ts dir conv_t env evsubs args t)
        with CannotPrune -> report (Err dbg)
      end
    else Err dbg

and meta_deldeps dir ts conv_t env (ev, subs as evsubs) args (h, args' as t) sigma dbg =
  if is_aggressive () then
    begin
      try 
	let (sigma', evsubs', args'') = remove_non_var env sigma evsubs args in 
        report (
          log_eq_spine env "Meta-DelDeps" conv_t (mkEvar evsubs, args) t (dbg, sigma') &&=
          switch dir (unify' ~conv_t ts env) (evsubs', args'') t)
      with CannotPrune -> Err dbg
    end
  else Err dbg

and meta_specialize dir ts conv_t env (ev, subs as evsubs) args (h, args' as t) sigma dbg =
  if !super_aggressive then
    begin
      try
        let (sigma', evsubst', args'') = specialize_evar env sigma evsubs args in 
        report (
          log_eq_spine env "Meta-Specialize" conv_t (mkEvar evsubs, args) t (dbg, sigma') &&=
          switch dir (unify' ~conv_t ts env) (evsubst', args'') t)
      with CannotPrune -> Err dbg
    end
  else Err dbg

and meta_reduce dir ts conv_t env (ev, subs as evsubs) args (h, args' as t) sigma dbg =
  (* Meta-Reduce: before giving up we see if we can reduce on the right *)
  if has_definition ts env h then
    begin
      let t' = evar_apprec ts env sigma (get_def_app_stack env t) in 
      report (
        log_eq_spine env "Meta-Reduce" conv_t (mkEvar evsubs, args) t (dbg, sigma) &&=
        switch dir (unify' ~conv_t ts env) (mkEvar evsubs, args) t')
    end
  else
    begin
      let t' = evar_apprec ts env sigma t in
      if not (eq_app_stack t t') then
        begin 
          report (
            log_eq_spine env "Meta-Reduce" conv_t (mkEvar evsubs, args) t (dbg, sigma) &&=
            switch dir (unify' ~conv_t ts env) (mkEvar evsubs, args) t')
        end
      else Err dbg
    end
    
and meta_eta dir ts conv_t env (ev, subs as evsubs) args (h, args' as t) sigma dbg =
  (* if the equation is [?f =?= \x.?f x] the occurs check will fail, but there is a solution: eta expansion *)
  if isLambda h && List.length args' = 0 then
    begin 
      report (
        log_eq_spine env "Lam-Eta" conv_t (mkEvar evsubs, args) t (dbg, sigma) &&=
        eta_match conv_t  ts env (destLambda h) (mkEvar evsubs, args))
    end
  else
    Err dbg

(* by invariant, we know that ev is uninstantiated *)
and instantiate ?(dir=Original) ts conv_t env 
    (ev, subs as evsubs) args (h, args' as t) sigma dbg =
  meta_inst dir ts conv_t env evsubs args t sigma dbg
  ||= meta_fo dir conv_t ts env (evsubs, args) t sigma
  ||= meta_deldeps dir ts conv_t env evsubs args t sigma
  ||= meta_specialize dir ts conv_t env evsubs args t sigma
  ||= meta_reduce dir ts conv_t env evsubs args t sigma
  ||= meta_eta dir ts conv_t env evsubs args t sigma
      
and should_try_fo args (h, args') =
  List.length args > 0 && List.length args' >= List.length args

(* ?e a1 a2 = h b1 b2 b3 ---> ?e = h b1 /\ a1 = b2 /\ a2 = b3 *)
and meta_fo dir conv_t ts env (evsubs, args) (h, args' as t) sigma dbg =
  if not (should_try_fo args t) then Err dbg
  else
    let (args'1,args'2) =
      CList.chop (List.length args'-List.length args) args' in
    begin report (
        (* Meta-FO *)
        log_eq_spine env "Meta-FO" conv_t (mkEvar evsubs, args) 
          t (dbg, sigma) &&= fun (dbg, sigma) ->
          if dir = Original then 
            unify' ts ~conv_t env (mkEvar evsubs, []) (h, args'1) (dbg, sigma) &&= 
            ise_list2 (unify_constr ts env) args args'2
          else
            unify' ts ~conv_t env (h, args'1) (mkEvar evsubs, []) (dbg, sigma) &&=
            ise_list2 (unify_constr ts env) args'2 args
      ) end

(* unifies ty with a product type from {name : a} to some Type *)
and check_product dbg ts env sigma ty (name, a) =
  let nc = Environ.named_context env in
  let naid = Namegen.next_name_away name (Termops.ids_of_named_context nc) in
  let nc' = (naid, None, a) :: nc in
  let sigma', univ = Evd.new_univ_variable Evd.univ_flexible sigma in
  let evi = Evd.make_evar (Environ.val_of_named_context nc') (mkType univ) in 
  let sigma'',v = Evarutil.new_pure_evar_full sigma' evi in
  let idsubst = Array.append [| mkRel 1 |] (id_substitution nc) in
    unify_constr ~conv_t:Reduction.CUMUL ts env ty (mkProd (Names.Name naid, a, mkEvar(v, idsubst))) (dbg, sigma'')

and eta_match conv_t ts env (name, a, t1) (th, tl as t) (dbg, sigma0 ) =
  let env' = Environ.push_rel (name, None, a) env in
  let t' = applist (lift 1 th, List.map (lift 1) tl @ [mkRel 1]) in
  let ty = Retyping.get_type_of env sigma0 (applist t) in
    check_product dbg ts env sigma0 ty (name, a) &&=
      unify_constr ~conv_t ts env' t1 t'

and conv_record dbg trs env evd t t' =
  let (c,bs,(params,params1),(us,us2),(ts,ts1),c1,(n,t2)) = check_conv_record t t' in
  let (evd',ks,_) =
    List.fold_left
      (fun (i,ks,m) b ->
	match n with
	| Some n when m = n -> (i,t2::ks, m-1) 
	| _ ->
	  let dloc = (Loc.dummy_loc, Evar_kinds.InternalHole) in
          let (i',ev) = Evarutil.new_evar env i ~src:dloc (substl ks b) in
	    (i', ev :: ks, m - 1))
      (evd,[],List.length bs) bs
  in
  report (
    log_eq_spine env "CS" Reduction.CONV t t' (dbg, evd') &&=
    ise_list2 (fun x1 x -> unify_constr trs env x1 (substl ks x)) params1 params &&=
    ise_list2 (fun u1 u -> unify_constr trs env u1 (substl ks u)) us2 us &&=
    unify' trs env (decompose_app c1) (c,(List.rev ks)) &&=
    ise_list2 (unify_constr trs env) ts ts1)

and swap (a, b) = (b, a) 

and unify_evar_conv ts env sigma0 conv_t t t' =
  let interesting log = (* if it's not just Reduce-Same *)
    match !log with 
    | Logger.Node (("Reduce-Same", _), _, true, _) -> false
    | _ -> true in
  stat_unif_problems := Big_int.succ_big_int !stat_unif_problems;
  Hashtbl.clear tbl;
  match unify_constr ~conv_t:conv_t ts env t t' (Logger.init, sigma0) with
  | Success (log, sigma') -> 
    if get_debug () && interesting log then
      begin
        Logger.dump "/tmp/unif.tex" print_eq log;
        Logger.dump2 log;
      end
    else ();
    Evarsolve.Success sigma'
  | Err log -> 
    if get_debug () then Logger.dump2 log;
    Evarsolve.UnifFailure (sigma0, Pretype_errors.NotSameHead)
  
let use_munify () = !munify_on
let set_use_munify b = 
  if b then try Evarconv.set_evar_conv unify_evar_conv with _ -> ();  
  munify_on := b

let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; 
  Goptions.optdepr = false;
  Goptions.optname = "Enable use of new unification algorithm";
  Goptions.optkey = ["Use";"Unicoq"];
  Goptions.optread = use_munify;
  Goptions.optwrite = set_use_munify;
}

(* Now the real tactic. *)

open Proofview
open Notations

let munify_tac gl x y =
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let evars evm = V82.tactic (Refiner.tclEVARS evm) in
  let res = unify_constr (Conv_oracle.get_transp_state (Environ.oracle env)) env x y (Logger.init, sigma) in
    match res with
    | Success (log, evm) -> evars evm
    | Err _ -> Tacticals.New.tclFAIL 0 (str"Unification failed")

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
