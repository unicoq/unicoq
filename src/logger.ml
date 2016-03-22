
type 'a nlog =
  Initial
  | Node of 'a * 'a nlog ref * bool * ('a nlog ref) list

type log_elem = string * (Reduction.conv_pb * string * string)

type log = log_elem nlog ref

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

let rec pad l = 
  if l <= 0 then () else (Printf.printf "_"; pad (l-1))

let rec depth l =
  match !l with
  | Initial -> 0
  | Node (_, p, _, _) -> depth p + 1

let print_node (s, (conv_t, c1, c2)) =
  output_string stdout c1;
  output_string stdout (if conv_t = Reduction.CONV then " =?= " else " =<= ");
  output_string stdout c2;
  output_string stdout " (";
  output_string stdout s;
  output_string stdout ")"

let newNode print v l =
  if print then
    begin
      pad (depth l);
      print_node v;
      output_string stdout "\n";
    end;
  let n = ref (Node (v, l, true, [])) in
  match !l with
  | Initial -> n
  | Node (v', p, s, c) -> 
    l := Node (v', p, s, (n::c));
    n
    
let report b l =
  match !l with
  | Initial -> l
  | Node (v, p, _, c) ->
    l := Node (v, p, b, c);
    if is_init p then l else p

let reportSuccess = report true

let reportErr = report false

let rec to_parent l =
  match !(parent l) with
  | Initial -> l
  | Node (_, p, _, _) -> to_parent (parent l)

let rec print_to_stdout i l =
  match !l with
  | Initial -> ()
  | Node (n, _, st, ls) ->
    pad i;
    print_node n;
    if st then
      output_string stdout " OK\n"
    else
      output_string stdout " ERR\n";
    List.iter (print_to_stdout (i+1)) (List.rev ls)

let print_to_stdout l = print_to_stdout 0 (to_parent l)

let print_latex s p l =
  let f = open_out_gen [Open_append; Open_creat] 0o666 s in
  let rec dump l =
    match !l with
    | Initial -> ()
    | Node ((s, n), _, true, ls) ->
      output_string f "\\fbox{$\\inferrule*[left=";
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

let print_latex s p l =
  if s = "" then
    Printf.printf "Warning: no LaTex file set with [Set Unicoq LaTex File 'file']. No LaTex output will be generated.\n"
  else
    try
      print_latex s p (to_parent l)
    with Sys_error p -> Printf.printf "Logger error: '%s'\n" p
