
type 'a nlog =
  Initial
  | Node of 'a * 'a nlog ref * bool * ('a nlog ref) list

type log_elem = string * (Reduction.conv_pb * string * string)

type log = log_elem nlog ref

val init : log

val reportSuccess : log -> log

val reportErr : log -> log

val newNode : bool -> log_elem -> log -> log

val print_latex : string ->
  (out_channel -> (Reduction.conv_pb * string * string) -> unit) ->
  log -> unit

val print_to_stdout : log -> unit
