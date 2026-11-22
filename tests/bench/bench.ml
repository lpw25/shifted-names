open Lambda
let n = Big_int_Z.big_int_of_int
let z = Big_int_Z.zero_big_int
let bv i = Tvar { v_label = None; v_index = n i }
let fv x = Tvar { v_label = Some x; v_index = z }
let time name f =
  Gc.compact ();
  let t = Unix.gettimeofday () in
  let r = f () in
  Printf.printf "%-34s %8.3f s\n%!" name (Unix.gettimeofday () -. t); r
let rec size = function Tapp (a, b) -> 1 + size a + size b | Tlam b -> 1 + size b | _ -> 1
let fuel = n 1_000_000_000

(* λ^d. (#0 #1 ... #(d-1) x) : open every binder with a name, close back *)
let deep d =
  let rec body i acc = if i = d then acc else body (i + 1) (Tapp (acc, bv i)) in
  let rec lams i t = if i = 0 then t else lams (i - 1) (Tlam t) in
  lams d (body 0 (fv "x"))
let open_close t d =
  let rec go k sc t = if k = d then t else
      (match t with
       | Tlam b -> let x = name (n k) in
         let o = go (k + 1) (Big_int_Z.pred_big_int sc) (topen_f sc x b) in
         Tlam (tclose_f sc x o)
       | _ -> t) in
  go 0 (n d) t
(* instantiate the outermost binder of λ^d. body, under d-1 binders *)
let inst_deep t u = match t with Tlam b -> tinst_f z u b | _ -> t
(* a balanced tree of applications of the free names v0..v(w-1) *)
let rec tree lo hi = if hi - lo = 1 then fv (name (n lo)) else
    let m = (lo + hi) / 2 in Tapp (tree lo m, tree m hi)
let wide_sub w = let rec go i a = if i = w then a else go (i + 1) (sub_comp (sub_one (name (n i)) (Tconst (n i))) a) in go 0 sub_id
let chain_sub w = let rec go i a = if i = w then a else
    go (i + 1) (sub_comp a (sub_ren (name (n i)) (name (n (i + 1))))) in go 0 sub_id
(* Church numerals *)
let church k = let rec go i = if i = 0 then bv 0 else Tapp (bv 1, go (i - 1)) in Tlam (Tlam (go k))
let mult = Tlam (Tlam (Tlam (Tapp (bv 2, Tapp (bv 1, bv 0)))))
let rec count = function Tlam b -> count b | Tapp (_, a) -> 1 + count a | _ -> 0

let () =
  let arg i d = try int_of_string Sys.argv.(i) with _ -> d in
  let d = arg 1 400 and w = arg 2 200 and c = arg 3 30 in
  let t = deep d in
  let t' = time (Printf.sprintf "open/close %d binders" d) (fun () -> open_close t d) in
  assert (t' = t);
  ignore (time (Printf.sprintf "instantiate under %d binders" d) (fun () -> inst_deep t (Tconst z)));
  let tw = tree 0 w in
  let a = time (Printf.sprintf "compose %d singletons" w) (fun () -> wide_sub w) in
  let r = time (Printf.sprintf "apply %d-entry substitution" w) (fun () -> tsubst z z a tw) in
  assert (size r = size tw);
  let ch = time (Printf.sprintf "compose %d renamings" w) (fun () -> chain_sub w) in
  ignore (time (Printf.sprintf "apply %d-renaming chain" w) (fun () -> tsubst z z ch tw));
  let seq = time (Printf.sprintf "%d substitutions one by one" w) (fun () ->
      let rec go i t = if i = w then t else go (i + 1) (tsubst z z (sub_one (name (n i)) (Tconst (n i))) t) in go 0 tw) in
  assert (seq = r);
  let m = time (Printf.sprintf "normalise mult %d %d" c c) (fun () -> nf fuel z (Tapp (Tapp (mult, church c), church c))) in
  assert (count m = c * c);
  print_endline "bench done"
