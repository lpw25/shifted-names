open Lambda
let z = Big_int_Z.zero_big_int
let n i = Big_int_Z.big_int_of_int i
let rec show = function
  | Tvar v -> (match v.v_label with
               | None -> "#" ^ Big_int_Z.string_of_big_int v.v_index
               | Some x -> x ^ "_" ^ Big_int_Z.string_of_big_int v.v_index)
  | Tconst k -> Big_int_Z.string_of_big_int k
  | Tapp (a, b) -> "(" ^ show a ^ " " ^ show b ^ ")"
  | Tlam b -> "(\\. " ^ show b ^ ")"
let bv i = Tvar { v_label = None; v_index = n i }
let fv x i = Tvar { v_label = Some x; v_index = n i }
(* scope 0: \. (#0 x_0 y_0) *)
let t = Tlam (Tapp (Tapp (bv 0, fv "x" 0), fv "y" 0))
let () = print_endline ("t            = " ^ show t)
let c = tclose z "x" t
let () = print_endline ("close x t    = " ^ show c)
let o = topen z "x" c
let () = print_endline ("open x (..)  = " ^ show o)
let () = print_endline ("round trip ok: " ^ string_of_bool (o = t))
(* scope 1 body: (#0 #0 x_0); instantiate #0 with closed \.#0 *)
let body = Tapp (Tapp (bv 0, bv 0), fv "x" 0)
let u = Tlam (bv 0)
let r = LS.subst (n 1) z (inst z u) body
let () = print_endline ("inst (\\.#0) (#0 #0 x_0) = " ^ show r)
(* under a binder: \. (#0 #1) at scope 1, instantiate #1 *)
let body2 = Tlam (Tapp (bv 0, bv 1))
let r2 = LS.subst (n 1) z (inst z u) body2
let () = print_endline ("inst (\\.#0) (\\. #0 #1) = " ^ show r2)
let () = assert (o = t)
let () = assert (show r = "(((\\. #0) (\\. #0)) x_0)")
let () = assert (show r2 = "(\\. (#0 (\\. #0)))")
let () = print_endline "extraction smoke test passed"
