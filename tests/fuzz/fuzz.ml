(* Normal-form fuzzer: random adjustment expressions are grouped by their
   meaning under a fixed family of random interpretations of the atoms;
   two expressions with the same meaning but different normal forms are
   reported (a missing case in the normaliser, or an unlucky family). *)
open Norm
let z = Big_int_Z.big_int_of_int
let iz = Big_int_Z.int_of_big_int

let labels = [| LNone; LCon "a"; LCon "b" |]
let probe_labels = [ None; Some "a"; Some "b"; Some "c" ]
let pick a = a.(Random.int (Array.length a))

let rec gen_a d nat =
  if d <= 0 then (match Random.int 3 with 0 -> AId | _ -> if nat > 0 then AAtom (z (Random.int nat)) else AId)
  else match Random.int 10 with
    | 0 -> AId
    | 1 | 2 -> if nat > 0 then AAtom (z (Random.int nat)) else AId
    | 3 | 4 -> ACompose (gen_a (d-1) nat, gen_a (d-1) nat)
    | 5 -> AOuter (pick labels, gen_a (d-1) nat)
    | 6 | 7 -> AInner (pick labels, gen_t (d-1) nat, gen_a (d-1) nat)
    | _ -> ALift (pick labels, gen_a (d-1) nat)
and gen_t d nat =
  match Random.int 5 with
  | 0 -> TBindE (z (Random.int 2), if d > 0 && Random.bool () then PComp (gen_a (d-1) nat, PId) else PId)
  | _ -> TVarE (pick labels, z (Random.int 2))

(* Interpretations: atom-free expressions, whose terms are tagged per atom
   so that different atoms are told apart. *)
let tenv = List.init 64 (fun i -> i)
let rec retag k = function
  | TBindE (u, p) -> TBindE (Big_int_Z.add_big_int u (z (2 * k)), p)
  | TShiftE (h, t) -> TShiftE (h, retag k t)
  | t -> t
let rec retag_a k = function
  | ACompose (a, b) -> ACompose (retag_a k a, retag_a k b)
  | AOuter (h, a) -> AOuter (h, retag_a k a)
  | AInner (h, t, a) -> AInner (h, retag k t, retag_a k a)
  | ALift (h, a) -> ALift (h, retag_a k a)
  | a -> a
let interp () =
  List.init 2 (fun k -> aeden [] tenv [] [] (retag_a (20 + k) (gen_a 4 0)))
(* The free interpretation: atom [k] sends each probe variable to its own
   term, so the result shows which variable reached which atom and, in the
   payload, what was done after. *)
let free k =
  let e = ref AId in
  List.iteri (fun li l ->
      for i = 1 downto 0 do
        e := AInner (l, TBindE (z (2 + 16 * k + 4 * li + i), PId), !e)
      done) [ LNone; LCon "a"; LCon "b"; LCon "c" ];
  aeden [] tenv [] [] !e
(* A renaming atom: [k] sends everything to distinct variables of a label
   of its own. *)
let fresh k =
  let lab = LCon ("f" ^ string_of_int k) in
  let e = ref AId in
  List.iter (fun l ->
      for i = 3 downto 0 do
        e := AInner (l, TVarE (lab, z (10 * (match l with LNone -> 0 | LCon "a" -> 1 | LCon "b" -> 2 | _ -> 3) + i)), !e)
      done) [ LNone; LCon "a"; LCon "b"; LCon "c" ];
  aeden [] tenv [] [] !e
let interps = ref []

let probes =
  List.concat_map (fun l -> List.init 7 (fun i -> { v_label = l; v_index = z i })) probe_labels

let meaning e =
  List.map (fun aenv -> let r = aeden [] tenv aenv [] e in List.map (rapply r) probes) !interps

let rec pl = function LNone -> "." | LCon s -> s | LAtom n -> "l" ^ Big_int_Z.string_of_big_int n
let rec pa = function
  | AId -> "id" | AAtom n -> "s" ^ Big_int_Z.string_of_big_int n
  | ACompose (a, b) -> "(" ^ pa a ^ " o " ^ pa b ^ ")"
  | AOuter (h, a) -> "out[" ^ pl h ^ "](" ^ pa a ^ ")"
  | AInner (h, t, a) -> "in[" ^ pl h ^ ":=" ^ pt t ^ "](" ^ pa a ^ ")"
  | ALift (h, a) -> "lift[" ^ pl h ^ "](" ^ pa a ^ ")"
and pt = function
  | TVarE (h, i) -> pl h ^ Big_int_Z.string_of_big_int i
  | TBindE (u, p) -> "u" ^ Big_int_Z.string_of_big_int u ^ pp p
  | TShiftE (h, t) -> "sh[" ^ pl h ^ "]" ^ pt t
and pp = function PId -> "" | PAtom n -> "<p" ^ Big_int_Z.string_of_big_int n ^ ">" | PComp (a, p) -> "<" ^ pa a ^ pp p ^ ">" | PShift (h, p) -> "<sh" ^ pl h ^ pp p ^ ">"

let rec pn : ntgt -> string = function
  | NVar (h, i) -> pl h ^ Big_int_Z.string_of_big_int i
  | NBind (u, w, b) -> "u" ^ Big_int_Z.string_of_big_int u ^ "<" ^ pw w ^ ">"
and ptl : tlist -> string = function TNil -> "" | TCons (t, TNil) -> pn t | TCons (t, r) -> pn t ^ "," ^ ptl r
and ps : seg -> string = function
  | SNil0 -> "" | SEnt (h, ts, m, r) -> pl h ^ "[" ^ ptl ts ^ "|" ^ Big_int_Z.string_of_big_int m ^ "] " ^ ps r
and pw : word -> string = function
  | WEnd s -> "{" ^ ps s ^ "}"
  | WAtom (s, l, a, w) ->
      "{" ^ ps s ^ "} " ^ String.concat "" (List.map (fun (h, n) -> "^" ^ pl h ^ Big_int_Z.string_of_big_int n) l)
      ^ "s" ^ Big_int_Z.string_of_big_int a ^ " " ^ pw w

let () =
  let iters = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 20000 in
  let seed = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 1 in
  Random.init seed;
  interps := [ [free 0; free 1]; [fresh 0; fresh 1]; [free 0; fresh 1]; [fresh 0; free 1] ] @ List.init 6 (fun _ -> interp ());
  let tbl = Hashtbl.create 10000 in
  let bad = ref 0 and failed = ref 0 in
  for _ = 1 to iters do
    let e = gen_a 5 2 in
    match anorm [] (z 2) e with
    | None -> incr failed
    | Some w ->
        let m = meaning e in
        (match Hashtbl.find_opt tbl m with
         | None -> Hashtbl.add tbl m (e, w)
         | Some (e', w') ->
             if w <> w' then begin
               incr bad;
               if !bad <= 15 then
                 Printf.printf "DIFFERENT NORMAL FORMS\n  %s\n    = %s\n  %s\n    = %s\n%!" (pa e') (pw w') (pa e) (pw w)
             end)
  done;
  Printf.printf "%d expressions, %d meanings, %d normaliser failures, %d mismatches\n"
    iters (Hashtbl.length tbl) !failed !bad
