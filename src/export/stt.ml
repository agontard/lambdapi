(** Base module for translating lp proofs encoded in simple type theory. *)

open Lplib open Extra
open Common open Pos open Error
open Parsing open Syntax
open Core

let log = Logger.make 'x' "xprt" "export"
let log = log.pp

module Qid = struct type t = Term.qident let compare = Stdlib.compare end
module QidMap = Map.Make(Qid)

(** Set renaming map from file. *)

let rmap = ref StrMap.empty
let codom = ref StrSet.empty

let add_renaming pos s1 s2 =
  let f = function
    | None -> Some s2
    | Some s2' ->
      fatal pos "\"%s\" renamed to both \"%s\" and \"%s\"" s1 s2' s2
  in
  if Logger.log_enabled() then log "rename %s into %s" s1 s2;
  rmap := StrMap.update s1 f !rmap;
  codom := StrSet.add s2 !codom

let set_renaming : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(string,{elt=(p,lp_id);pos=pos_id});pos} ->
      if p = [] then add_renaming pos lp_id string
      else fatal pos_id "Qualified identifier."
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

(** Set symbols whose declarations have to be erased. *)

let mapping = ref QidMap.empty

let add_mapping qid string =
  if Logger.log_enabled() then
    log "map %a to \"%s\"" Pretty.qident qid string;
  mapping := QidMap.add qid.elt string !mapping

let set_mapping : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(string,lp_qid);_} -> add_mapping lp_qid string
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

let current_mp = Stdlib.ref []

let is_mapped id =
  QidMap.mem ([],id) !mapping || QidMap.mem (!current_mp,id) !mapping

(** Set encoding. *)

type pattern_tree =
  | Leaf of string
  | Branch of pattern_tree * (pattern_tree * bool) list

(** regexp matching either ($n) or $n *)
let arg n =
  let n' = Int.to_string n in
  Str.regexp ({|\((\$|} ^ n' ^ {|)\|\$|} ^ n' ^ {|\)|})

let pattern_tree_of_string arity s =
  let rec t_of_s i s =
    if i == arity + 1 then Leaf s
    else match Str.full_split (arg i) s with
    | [] -> assert false
    | Text s' :: rest -> Branch (t_of_s (i+1) s',t_of_l i rest)
    | l -> Branch(Leaf "", t_of_l i l)
  and t_of_l i l = match l with
    | [] -> []
    | [Delim d] -> [(Leaf "", String.contains d '(')]
    | Delim d :: Text s :: rest ->
      (t_of_s (i+1) s, String.contains d '(') :: t_of_l i rest
    | _ -> assert false
  in t_of_s 1 s

let pattern_tree_iter of_string of_pvar of_var t =
  let rec pattern_tree_iter index t = match t with
    | Leaf s -> of_string s
    | Branch (hd,tl) -> pattern_tree_iter (index+1) hd;
      List.iter (fun (t,paren) -> (if paren then of_pvar else of_var) index;
        pattern_tree_iter (index+1) t) tl
  in pattern_tree_iter 1 t

type notation_kind =
| Trivial of int
| Regular of bool (* enclosed *) * int (* arity *) * pattern_tree
| Quantifier of bool (* enclosed *) * int (* arity *) * pattern_tree

let mk_trivial pos s =
  let n = try int_of_string s with
    | Failure _ -> fatal pos {|trivial pattern syntax: "trivial (int)"|}
  in if n > 0 then Trivial n else fatal pos "Arity must be strictly positive."

let notations : notation_kind QidMap.t ref = ref QidMap.empty
let add_notation qid nota = notations := QidMap.add qid nota !notations

let parse_pat pos pat =
  let find_prefix prefix s = if String.is_prefix prefix s
    then let n = String.length prefix in
      (true, String.sub s n (String.length s - n))
    else (false, s)
  in let (is_triv,pat) = find_prefix "trivial " pat in
  if is_triv then mk_trivial pos pat
  else let (is_enclosed,pat) = find_prefix "enclosed " pat in
  let (is_quantifier,pat) = find_prefix "quantifier " pat in
  let arity_regexp = Str.regexp {|^\([0-9]+\)[ \t]*| \(.+\)|} in
  if not (Str.string_match arity_regexp pat 0)
  then fatal pos "Cannot find arity in pattern: \"%s\"" pat
  else let arity = int_of_string (Str.matched_group 1 pat) in
  let pat = Str.matched_group 2 pat in
  if not is_quantifier
  then Regular (is_enclosed, arity, pattern_tree_of_string arity pat)
  else match Str.split_delim (Str.regexp {|\$x|}) pat with
  | [hd;tl] ->
    let to_tree s =
      let simple_arg = Str.regexp ({|\$|} ^ Int.to_string arity) in
      let s = Str.global_substitute simple_arg (fun _ -> "$1") s in
      pattern_tree_of_string 1 s
    in let pat_tree = Branch(to_tree hd, [(to_tree tl, false)]) in
    Quantifier (is_enclosed, arity, pat_tree)
  | _ -> fatal pos "%s\n Faulty pattern: \"%s\""
    "Variable pattern must happen exactly once." pat

let set_notations : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(pat,({elt=qid;_} as lp_qid));pos} ->
        if Logger.log_enabled() then
          log "builtin \"%s\" = %a" pat Pretty.qident lp_qid;
        add_notation qid (parse_pat pos pat)
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

let is_encoded id =
  QidMap.mem ([],id) !notations || QidMap.mem (!current_mp,id) !notations

(** Map from symbol name to number of type variables (>0). A symbol with no
    entry is not polymorphic (arity =0). *)

let tvs_map : (int StrMap.t ref) = ref StrMap.empty

let set_tvs_map (fname:string): unit =
  let ic = open_in_bin fname in
  tvs_map := StrMap.add "el" 1 (input_value ic);
  close_in ic

(** Basic printing functions. We use Printf for efficiency reasons. *)

let out = Printf.printf

let char = output_char
let string = output_string

let prefix pre elt oc x = string oc pre; elt oc x
let suffix elt suf oc x = elt oc x; string oc suf

let list elt sep oc xs =
  match xs with
  | [] -> ()
  | x::xs -> elt oc x; List.iter (prefix sep elt oc) xs

(** Translation of identifiers. *)

let check : (popt -> string -> unit) Stdlib.ref = ref (fun _ _ -> ())

let translate_ident {elt=s;pos}: string =
  try StrMap.find s !rmap
  with Not_found ->
    if StrSet.mem s !codom then s^"__alt__" else (!check pos s; s)

let ident oc id = string oc (translate_ident id)

let param_id oc idopt =
  match idopt with
  | Some id -> ident oc id
  | None    -> char oc '_'

let param_ids = list param_id " "

let path_elt pos oc id = !check pos id; string oc id

let path oc {elt;pos} = list (path_elt pos) "." oc elt

let alias = Stdlib.ref StrMap.empty

let rec qident oc {elt=((mp,id) as qid);pos} =
  match mp with
  | [] ->
    begin match QidMap.find_opt (!current_mp,id) !mapping with
      | None ->
        begin match QidMap.find_opt ([],id) !mapping with
          | None -> ident oc {elt=id;pos}
          | Some s -> string oc s
        end
      | Some s -> string oc s
    end
  | [p] ->
    begin match StrMap.find_opt p !alias with
      | Some mp -> qident oc {elt=(mp,id);pos}
      | None ->
        match QidMap.find_opt qid !mapping with
        | None -> path oc {elt=mp;pos}; char oc '.'; ident oc {elt=id;pos}
        | Some s -> string oc s
    end
  | _::mp ->
    begin match QidMap.find_opt (mp,id) !mapping with
    | None -> path oc {elt=mp;pos}; char oc '.'; ident oc {elt=id;pos}
    | Some s -> string oc s
    end

(** Translation of terms. *)

let stt = Stdlib.ref false
let use_implicits = Stdlib.ref false
let use_notations = Stdlib.ref false

(* redefinition of p_get_args ignoring P_Wrap's. *)
let p_get_args : p_term -> p_term * p_term list = fun t ->
  let rec p_get_args t acc =
    match t.elt with
    | P_Appl(t, u) -> p_get_args t (u::acc)
    | P_Wrap t -> p_get_args t acc
    | _ -> t, acc
  in p_get_args t []

let combine_arguments (ps : p_params list) ps' =
  if ps = [] then ps' else
  let (hd,(l,t,b)) = List.split_last ps in
  match ps' with
  | (l',t',b') :: tl when Option.eq eq_p_term t t' && b = b' ->
    hd @ (l @ l',t,b) :: tl
  | _ -> ps @ ps'

let rec unwrap t = match t with P_Wrap t -> unwrap t.elt | _ -> t

let app of_string of_term with_p of_args default needs_parentheses t =
  let enclose enclosed f =
    if needs_parentheses && not enclosed
    then (of_string "(" ; f() ; of_string ")")
    else f()
  in let (h,ts) = p_get_args t in
  let default() = enclose false (fun() -> default h ts) in
  if !stt then
    match h.elt with
    | P_Iden({elt;_},b) ->
        begin match QidMap.find_opt elt !notations with
        | Some(Regular(enclosed,arity,pat)) when arity = List.length ts ->
          let on_nth f n = f (List.nth ts (n-1)) in
          enclose enclosed (fun () ->
            pattern_tree_iter of_string (on_nth with_p) (on_nth of_term) pat
          )
        | Some(Quantifier(enclosed,arity,pat))
          when arity = List.length ts ->
          let rec get_args_body ts accl acct =
            match unwrap (List.nth ts (arity - 1)).elt with
            | P_Abst(args,t) -> let (h,ts) = p_get_args t in
              let new_args = combine_arguments accl args in
              let is_same_symb = match unwrap h.elt with
              | P_Iden ({elt=qid;_},b') -> qid = elt && b = b'
              | _ -> false
              in if is_same_symb && arity = List.length ts
              then get_args_body ts new_args t
              else (new_args, t)
            | _ -> (accl,acct)
          in let (args,body) = get_args_body ts [] t in
          if args == [] then default() else
          let of_pvar n = assert (n = 2); with_p body in
          let of_var n = if n = 1 then of_args args
            else (assert (n = 2); of_term body)
          in enclose enclosed (fun() ->
            pattern_tree_iter of_string of_pvar of_var pat
          )
        | Some(Trivial n) when List.length ts >= n ->
          (if needs_parentheses then with_p else of_term) (List.nth ts (n-1))
        | _ -> default()
        end
    | _ -> default()
  else default()

let is_lem x = is_opaq x || is_priv x

(** Set required file. *)

let require = ref None

let set_requiring : string -> unit = fun f -> require := Some f
