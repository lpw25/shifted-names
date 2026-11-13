(** * The canonical layered word

    [Layered.fold] returns a layered word that means what the expression
    means.  [canon] puts it in canonical form, one step at a time from
    the end: [ccons s K] is the canonical word of the segment [s]
    followed by the canonical word [K], and [catom] that of a lifted
    atom followed by [K].

    A term of a segment has the rest of the word as its payload, after a
    word of its own when its payload has atoms that the rest does not
    have.  A term stands in the last segment whose rest is its payload:

    - when the first segments of [K] do nothing to named variables that
      the rest can tell from the identity, the terms of [s] join a later
      segment, carried there by bound variables ([thread]);
    - when the terms of the first segment of [K] are all on bound
      variables, the order between payloads ([above]) decides which of
      the two segments goes first ([swap]);
    - what a term's payload does after its last atom goes on the line
      ([tsplit]), and a term whose payload ends with the atom in front
      of it goes in front of that atom ([hop_at]);
    - otherwise [s] is a new first segment, and the variables between it
      and [K] are put in canonical form: each goes on as the
      representative of its key ([Retarget.reroute_g]), and the bound
      ones are numbered in the order of first use ([Retarget.renum]). *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Layered LayeredOrder Canon Keys Retarget.
Import ListNotations.

Section Canonical.

Variable F : order.
Variable ntm : nat.

Definition entry_of (s : seg) (g : lexp) : option (list ntgt * nat) :=
  match sfind F g s with Some e => let '(ts, m) := ofe e in Some (tl_list ts, m) | None => None end.

Definition no_tails (s : seg) : bool :=
  forallb (fun t => match ttail t with None => true | Some _ => false end) (stargets s).

(** ** The variables between a segment and the word after it *)
Definition iface (s : seg) (K : lword) : seg * seg :=
  let n1 := match K with
            | LS s1 :: _ => tlen (fst (bent F s1))
            | LA L _ :: _ => lcn F L LNone
            | [] => 0
            end in
  let clim := match K with LA L _ :: _ => Some (lcn F L LNone) | _ => None end in
  let sa := match reroute_g F ntm s K with Some x => x | None => s end in
  match renum F ntm clim n1 sa with Some p => p | None => (sa, SNil) end.

(** ** Joining a later segment *)

(** A renaming of named variables that the word [K] cannot tell from the
    identity. *)
Definition same_rest (sg : seg) (K : lword) : bool :=
  match sg with
  | SNil => true
  | _ => forallb (fun '(g, ts, m) =>
           Nat.eqb (tlen ts) m
           && forallb (fun j => match tnth ts j with
                                | NVar g' i' => okey_eqb (vfollow F K g' i') (vfollow F K g j)
                                | _ => false
                                end) (seq 0 (tlen ts))) (ents sg)
  end.

(** [sig] is what the segments passed so far do to named variables; the
    segment found is the last one whose rest cannot tell it from the
    identity. *)
Fixpoint scan (sig : seg) (K : lword) (j : nat) : option nat :=
  match K with
  | LS s1 :: K' =>
      match fcomp F ntm s1 sig with
      | Some c => let sg := sdrop_none c in
                  if has_terms sg then None
                  else if same_rest sg K' then (match scan sg K' (S j) with Some j' => Some j' | None => Some (S j) end)
                  else scan sg K' (S j)
      | None => None
      end
  | _ => None
  end.

(** A term that can be carried: the identity payload, or a tail that
    only renames bound variables. *)
Definition settled (t : ntgt) : bool :=
  match t with
  | NBind u (WEnd SNil) None => u <? ntm
  | NBind u _ _ => (u <? ntm) && match ttail t with Some A => settled_tail A | None => false end
  | _ => false
  end.

(** [s] as its renaming [sa] followed by its terms on bound variables. *)
Definition unterm (s : seg) : option (seg * list ntgt) :=
  match fcomp F ntm (shseg LNone (nterms s)) s with
  | Some s1 =>
      let '(es, _) := rents (ents s1) 0 in
      let '(_, T) := rents (ents s) 0 in
      match mkseg F es, tfront F T SNil with
      | Some sa, Some eT =>
          match fcomp F ntm eT sa with
          | Some s2 => if seg_eqb s2 s && forallb (tdistb F) T && sdistb F sa then Some (sa, T) else None
          | None => None
          end
      | _, _ => None
      end
  | None => None
  end.

(** The part of a segment for the bound label. *)
Definition bpart_o (A : seg) : option seg :=
  match sfind F LNone A with
  | Some e => Some (match ofe e with (TNil, 0) => SNil | (ts, m) => SEnt LNone ts m SNil end)
  | None => None
  end.

(** A term carried past a segment: its tail goes through the segment. *)
Definition tshift (s1 : seg) (t : ntgt) : option ntgt :=
  match ttail t with
  | Some A =>
      obind (obind (fcomp F ntm s1 A) bpart_o) (fun B => if has_terms B then None else Some (tset t B))
  | None => Some t
  end.

(** A term under [d] more bound variables. *)
Definition blift (d : nat) (t : ntgt) : ntgt :=
  match d, t with
  | 0, _ => t
  | _, NBind u (WEnd N) None =>
      match N with
      | SNil => t
      | _ => match fcomp F ntm (shseg LNone d) N with Some N' => NBind u (WEnd (sdrop_none N')) None | None => t end
      end
  | _, _ => match ttail t with
            | Some A => match fcomp F ntm (shseg LNone d) A with Some A' => tset t A' | None => t end
            | None => t
            end
  end.

Fixpoint tsh_chain (j : nat) (t : ntgt) (K : lword) : option ntgt :=
  match j, K with
  | 0, _ => Some t
  | S j', LS s1 :: K' => obind (tshift s1 t) (fun t' => tsh_chain j' t' K')
  | _, _ => None
  end.

Definition thread (j : nat) (T : list ntgt) (K : lword) : option lword :=
  obind (omapl (fun t => tsh_chain j t K) T) (fun T' => Canon.thread F ntm j T' K).

(** ** The order between payloads

    The height of a payload (how deep the terms it sends variables to
    go), then what it does to each variable, in the order of the
    variables. *)
Inductive fres3 := FT (t : ntgt) (d : nat) | FS (a : nat) (g : lexp) (i d : nat).

Fixpoint lfollow (l : lword) (h : lexp) (i : nat) : option fres3 :=
  match l with
  | [] => Some (FT (NVar h i) 0)
  | LS s :: r =>
      match seg_tgt F s h i with
      | Some (NVar g j) => lfollow r g j
      | Some t => Some (FT t (List.length r))
      | None => None
      end
  | LA L a :: r =>
      let c := lcn F L h in
      if i <? c then lfollow r h i else Some (FS a h (i - c) (List.length r))
  end.

Inductive hres := HVar (g : lexp) (i : nat) | HTerm (u : nat) (b : option nat) (d : nat) (code : list nat)
                | HStuck (a : nat) (g : lexp) (i d : nat) | HNone.

Definition follow (l : lword) (g : lexp) (i : nat) : hres :=
  match lfollow l g i with
  | Some (FT (NVar g' j) _) => HVar g' j
  | Some (FT (NBind u w b) d) => HTerm u b d (match w with WEnd SNil => [] | _ => wcode w end)
  | Some (FS a g' j d) => HStuck a g' j d
  | None => HNone
  end.

Fixpoint lcompare (x y : list nat) : comparison :=
  match x, y with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | p :: x', q :: y' => match Nat.compare p q with Eq => lcompare x' y' | c => c end
  end.

Definition lcmp3 (a b : lexp) : comparison := match lcmp F a b with Some c => c | None => Eq end.

Definition hcmp (x y : hres) : comparison :=
  match x, y with
  | HVar g i, HVar g' i' => match lcmp3 g g' with Eq => Nat.compare i i' | c => c end
  | HVar _ _, _ => Lt
  | _, HVar _ _ => Gt
  | HTerm u b d co, HTerm u' b' d' co' =>
      match Nat.compare u u' with
      | Eq => match Nat.compare d d' with
              | Eq => match b, b' with
                      | Some n, Some n' => match Nat.compare n n' with Eq => lcompare co co' | c => c end
                      | None, Some _ => Lt
                      | Some _, None => Gt
                      | None, None => lcompare co co'
                      end
              | c => c
              end
      | c => c
      end
  | HTerm _ _ _ _, _ => Lt
  | _, HTerm _ _ _ _ => Gt
  | HStuck a g i d, HStuck a' g' i' d' =>
      match Nat.compare a a' with
      | Eq => match Nat.compare d d' with
              | Eq => match lcmp3 g g' with Eq => Nat.compare i i' | c => c end
              | c => c
              end
      | c => c
      end
  | HStuck _ _ _ _, HNone => Lt
  | HNone, HStuck _ _ _ _ => Gt
  | HNone, HNone => Eq
  end.

Fixpoint lexc (a b : list hres) : comparison :=
  match a, b with
  | x :: a', y :: b' => match hcmp x y with Eq => lexc a' b' | c => c end
  | _, _ => Eq
  end.

Definition headv (labs : list lexp) (N : nat) (l : lword) : list hres :=
  flat_map (fun g => map (follow l g) (seq 0 N)) labs.

(** The heights of every rest of the word, the word itself first. *)
Fixpoint hts (labs : list lexp) (N : nat) (l : lword) : list nat :=
  match l with
  | [] => [0]
  | x :: r =>
      let H := hts labs N r in
      fold_right (fun h acc => match h with
                               | HTerm _ _ d _ => Nat.max acc (S (nth (List.length H - 1 - d) H 0))
                               | _ => acc
                               end) 0 (headv labs N (x :: r)) :: H
  end.

(** The payload [K] is above the payload [K'] (its rest). *)
Definition above (K K' : lword) : bool :=
  let labs := wlabs F K in
  let N := wbound K in
  let H := hts labs N K in
  match Nat.compare (nth 0 H 0) (nth 1 H 0) with
  | Gt => true
  | Lt => false
  | Eq => match lexc (headv labs N K) (headv labs N K') with Lt => false | _ => true end
  end.

(** ** Going behind the first segment *)

(** The four segments [sa; f1; n; rho] that [s; s1] becomes when [s]
    goes behind [s1], when they compose to the same. *)
Definition swap (s s1 : seg) : option (seg * seg * seg * seg) :=
  let sg1 := sdrop_none s1 in
  match sinv F sg1, unterm s with
  | Some (nu, R), Some (sa, T) =>
      match slifts F ntm (List.length T) s1,
            obind (omapl (tshift s1) T) (fun T' =>
              obind (sset F LNone TNil (List.length R) nu) (tfront F (map (blift (List.length R)) T'))),
            sset F LNone (tl_of R) 0 sg1 with
      | Some f1, Some n, Some rho =>
          match fcomp F ntm s1 s, obind (obind (fcomp F ntm f1 sa) (fcomp F ntm n)) (fcomp F ntm rho) with
          | Some c1, Some c2 =>
              if seg_eqb c1 c2 && forallb (settled) T && sdistb F f1 && sdistb F n && sdistb F rho
              then Some (sa, f1, n, rho) else None
          | _, _ => None
          end
      | _, _, _ => None
      end
  | _, _ => None
  end.

(** ** What a payload does after its last atom goes on the line *)

(** An inverse of a segment's renaming, for the bound label too: the
    variables after it come from their least source, or from one of [r]
    fresh bound variables in front. *)
Definition sinv_b (A : seg) : option (seg * list ntgt) :=
  let es := ents A ++ match sfind F LNone A with Some (Some _) => [] | _ => [(LNone, TNil, 0)] end in
  let srcs := fun t => match vmin F (named_srcs F A t) with
                       | Some w => Some w
                       | None => match findix t (fst (bent F A)) 0 with k :: _ => Some (LNone, k) | [] => None end
                       end in
  let nmiss := fun '(g, ts, m) => List.length (filter (fun i => match srcs (NVar g i) with None => true | _ => false end) (seq 0 m)) in
  let r := fold_right (fun e acc => nmiss e + acc) 0 es in
  fold_right (fun '(g, ts, m) acc =>
    obind acc (fun '(a, R) =>
      let pre := map (fun i => (i, srcs (NVar g i))) (seq 0 m) in
      let miss := filter (fun p => match snd p with None => true | _ => false end) pre in
      let tg := fun p => match snd p with
                         | Some (LNone, k) => NVar LNone (k + r)
                         | Some (h, k) => NVar h k
                         | None => NVar LNone (List.length R + index_of (fst p) (map fst miss) 0)
                         end in
      match sset F g (tl_of (map tg pre)) (tlen ts + match g with LNone => r | _ => 0 end) a with
      | Some a' => Some (a', R ++ map (fun p => NVar g (fst p)) miss)
      | None => None
      end)) (Some (SNil, [])) es.

Definition tsplit (t : ntgt) : option (seg * (nat -> option ntgt)) :=
  match t with
  | NBind u (WEnd N) None =>
      match N with SNil => None | _ => Some (sdrop_none N, fun _ => Some (NBind u (WEnd SNil) None)) end
  | _ =>
      match ttail t with
      | Some A =>
          if has_terms A || match sdrop_none A with SNil => false | _ => true end
          then Some (A, fun r => Some (tset t (match r with 0 => SNil | _ => shseg LNone r end)))
          else None
      | None => None
      end
  end.
Definition needs_split (t : ntgt) : bool := match tsplit t with Some _ => true | None => false end.

(** The segments [E'; N'; rho] that the segment of the one term [t]
    becomes, when they compose to it. *)
Definition split1 (t : ntgt) : option (option (seg * seg * seg)) :=
  match tsplit t with
  | Some (N, mk) =>
      match sinv_b N with
      | Some (nu, R) =>
          let r := List.length R in
          match obind (mk r) (fun t' => tfront F [t'] nu), slifts F ntm r N, sset F LNone (tl_of R) 0 SNil, tfront F [t] SNil with
          | Some E', Some N', Some rho, Some E0 =>
              match obind (fcomp F ntm N' E') (fcomp F ntm rho) with
              | Some c => if seg_eqb c E0 && sdistb F E' && sdistb F N' && sdistb F rho then Some (Some (E', N', rho)) else None
              | None => None
              end
          | _, _, _, _ => None
          end
      | None => None
      end
  | None => Some None
  end.

(** A segment as its renaming followed by one segment for each of its
    terms, when they compose to it. *)
Definition singles (s : seg) : option (seg * list (ntgt * seg)) :=
  match unterm s with
  | Some (sa, T) =>
      let ts := snd (fold_right (fun t '(d, acc) => (S d, blift d t :: acc)) (0, []) T) in
      match omapl (fun t => option_map (fun e => (t, e)) (tfront F [t] SNil)) ts with
      | Some tes =>
          match fold_left (fun acc te => obind acc (fun g => fcomp F ntm (snd te) g)) tes (Some sa) with
          | Some c => if seg_eqb c s && forallb (fun te => sdistb F (snd te)) tes then Some (sa, tes) else None
          | None => None
          end
      | None => None
      end
  | None => None
  end.

(** ** The canonical cons *)

Definition reroute_c (s : seg) (K : lword) : seg :=
  match reroute_g F ntm s K with Some s' => s' | None => s end.

(** Sending variables to their representatives, for the first [n]
    segments, from the last of them. *)
Fixpoint rr_up (n : nat) (l : lword) : lword :=
  match n, l with
  | S n', LS x :: r =>
      let r' := rr_up n' r in
      match r' with LS y :: _ => LS (reroute_c x r') :: r' | _ => LS x :: r' end
  | _, _ => l
  end.

(** After a join the segments passed have a new bound variable each:
    the variables between them are put in canonical form from the front,
    [n] segments deep, and what follows is consed as usual. *)
Fixpoint sweep (cc : seg -> lword -> option lword) (n : nat) (s : seg) (K : lword) : option lword :=
  match n, K with
  | S n', LS s1 :: K' =>
      let '(s', io) := iface s K in
      match (match io with SNil => Some s1 | _ => fcomp F ntm s1 io end) with
      | Some SNil => cc s' K'
      | Some s1' =>
          if has_terms s1' && has_terms s' then option_map (cons (LS s')) (sweep cc n' s1' K')
          else if has_terms s1' then obind (sweep cc n' s1' K') (cc s')
          else obind (cc s1' K') (cc s')
      | None => None
      end
  | _, _ => cc s K
  end.

Fixpoint recons (cc : seg -> lword -> option lword) (p : nat) (K : lword) : option lword :=
  match p, K with
  | S p', LS x :: r => obind (recons cc p' r) (fun r' => match x with SNil => Some r' | _ => cc x r' end)
  | _, _ => Some K
  end.

(** The terms that can be carried to the segment join it; the others
    stay in a segment [e] in front of the segment [em] of those that
    join. *)
Definition try_join (s s1 : seg) (K : lword) : option (nat * seg * option (seg * seg) * lword) :=
  if named_term s1 then None
  else match scan SNil K 0 with
       | Some j =>
           if match skipn (j - 1) K with
              | LS sj :: Kj1 => has_terms sj || above (LS sj :: Kj1) Kj1
              | _ => false
              end then
           obind (unterm s) (fun '(sa, T) =>
             if forallb settled T then
               let mv := map (fun t => match tsh_chain j t K with Some _ => true | None => false end) T in
               if forallb (fun b => b) mv then obind (thread j T K) (fun Kp => Some (j, sa, None, Kp))
               else
                 let M := map snd (filter fst (combine mv T)) in
                 match M with
                 | [] => None
                 | _ =>
                     let nm := List.length M in
                     let E := (fix go (l : list (bool * ntgt)) (k : nat) : list ntgt :=
                                 match l with
                                 | [] => []
                                 | (true, _) :: r => NVar LNone k :: go r (S k)
                                 | (false, x) :: r => blift nm x :: go r k
                                 end) (combine mv T) 0 in
                     match sset F LNone (tl_of E) nm SNil, tfront F M SNil, tfront F T SNil with
                     | Some e, Some em, Some eT =>
                         match fcomp F ntm em e, fcomp F ntm e sa with
                         | Some c, Some se =>
                             if seg_eqb c eT && sdistb F e && sdistb F em && sdistb F se then Some (j, se, Some (e, em), K) else None
                         | _, _ => None
                         end
                     | _, _, _ => None
                     end
                 end
             else None)
           else None
       | None => None
       end.

Definition try_swap (s s1 : seg) (K K' : lword) : option (seg * seg * seg * seg) :=
  if named_term s1 then None
  else if has_terms s1 then (if above K K' then None else swap s s1)
  else None.

Fixpoint ccons (fuel : nat) (s : seg) (K : lword) : option lword :=
  match fuel with
  | 0 => cons_seg F ntm s K
  | S f =>
      let cc0 := fun x K0 => match x with SNil => Some K0 | _ => ccons f x K0 end in
      if existsb needs_split (stargets s) then
        match singles s with
        | Some (sa, tes) =>
            obind (fold_right (fun te acc => obind acc (fun K0 =>
                     match split1 (fst te) with
                     | Some (Some (E', N', rho)) => obind (cc0 rho K0) (fun K1 => obind (cc0 N' K1) (ccons f E'))
                     | Some None => ccons f (snd te) K0
                     | None => None
                     end)) (Some K) tes) (cc0 sa)
        | None => None
        end
      else
      match K with
      | LS s1 :: K' =>
          if negb (has_terms s) || (bound_only s1 && (no_tails s || negb (has_terms s1))) then
            match fcomp F ntm s1 s with
            | Some SNil => Some K'
            | Some s' => ccons f s' K'
            | None => None
            end
          else
            match try_join s s1 K with
            | Some (j, se, Some (e, em), _) => obind (ccons f em K) (ccons f se)
            | Some (j, sa, None, Kp) =>
                match Kp with
                | LS p1 :: Kp' =>
                    match fcomp F ntm p1 sa with
                    | Some sm =>
                        match rr_up j (LS sm :: Kp') with
                        | LS x :: r => sweep (ccons f) j x r
                        | _ => None
                        end
                    | None => None
                    end
                | _ => None
                end
            | None =>
                match try_swap s s1 K K' with
                | Some (sa, f1, n, rho) =>
                    obind (ccons f rho K') (fun X => obind (ccons f n X) (fun K1 => obind (ccons f f1 K1) (ccons f sa)))
                | None =>
                    let '(s', io) := iface s K in
                    match io with
                    | SNil => Some (LS s' :: K)
                    | _ => obind (ccons f io K) (ccons f s')
                    end
                end
            end
      | LA L a :: Ka =>
          if has_terms s then
            let '(s', io) := iface s K in
            match io with
            | SNil => Some (LS s' :: K)
            | _ => obind (ccons f io K) (ccons f s')
            end
          else
            match wcomp F ntm (WAtom SNil L a (WEnd SNil)) (WEnd s) with
            | Some (WAtom sq L' a' (WEnd U)) =>
                obind (cc0 sq Ka) (fun K'' => Some (lpre U ++ LA L' a' :: K''))
            | _ => None
            end
      | [] => cons_seg F ntm s K
      end
  end.

(** ** A term whose payload ends in the atom in front of it

    Such a term goes in front of the atom: there its payload reaches the
    atom on the line. *)
Fixpoint remove_ix (J : list nat) (l : list ntgt) (k : nat) : list ntgt :=
  match l with [] => [] | x :: r => if mem k J then remove_ix J r (S k) else x :: remove_ix J r (S k) end.


(** After the atom, a variable that the atom gives out goes on as the
    payload's atom would send it. *)
Definition through_ok (S1 : seg) (L LT : list (lexp * nat)) (g : lexp) : bool :=
  match entry_of S1 g with
  | Some (ts, m) =>
      let cl := lcn F L g in
      let ct := lcn F LT g in
      Nat.eqb (m + cl) (ct + List.length ts)
      && forallb (fun j => match nth_error ts j with
                           | Some (NVar g' i) => lexp_eqb g' g && Nat.eqb (i + cl) (j + ct)
                           | _ => false
                           end) (seq cl (List.length ts - cl))
  | None => false
  end.

(** The inputs whose target has to change for that, each with the
    variable wanted. *)
Definition npairs (S1 : seg) (L LT : list (lexp * nat)) (g : lexp) : list ((lexp * nat) * (lexp * nat)) :=
  match entry_of S1 g with
  | Some (ts, m) =>
      let cl := lcn F L g in
      let ct := lcn F LT g in
      flat_map (fun j => match nth_error ts j with
                         | Some (NVar g' i) => if lexp_eqb g' g && Nat.eqb (i + cl) (j + ct) then [] else [((g, j), (g, j - cl + ct))]
                         | _ => []
                         end) (seq cl (List.length ts - cl))
  | None => []
  end.

Definition hop_cand (a : nat) (t : ntgt) : bool :=
  match t with
  | NBind u (WAtom A _ a' _) _ => Nat.eqb a a' && (u <? ntm) && match sdrop_none A with SNil => true | _ => false end
  | _ => false
  end.

Definition otgt_eqb (x y : option ntgt) : bool :=
  match x, y with Some p, Some q => ntgt_eqb p q | _, _ => false end.

Definition bthrough (S1 : seg) (L LT : list (lexp * nat)) (A : seg) : bool :=
  let cl := lcn F L LNone in
  let ct := lcn F LT LNone in
  let '(ts1, m1) := bent F S1 in
  let '(tsA, mA) := bent F A in
  Nat.eqb (m1 + cl + tlen tsA) (mA + ct + tlen ts1)
  && forallb (fun k => otgt_eqb (seg_tgt F S1 LNone (k + cl)) (seg_tgt F A LNone (k + ct)))
             (seq 0 (Nat.max (tlen ts1 - cl) (tlen tsA - ct))).

Definition bpairs (S1 : seg) (L LT : list (lexp * nat)) (A : seg) : list ((lexp * nat) * (lexp * nat)) :=
  let cl := lcn F L LNone in
  let ct := lcn F LT LNone in
  let '(ts1, m1) := bent F S1 in
  let '(tsA, mA) := bent F A in
  flat_map (fun k => match seg_tgt F S1 LNone (k + cl), seg_tgt F A LNone (k + ct) with
                     | Some (NVar g i), Some (NVar g' i') => if veqb (g, i) (g', i') then [] else [((LNone, k + cl), (g', i'))]
                     | _, _ => []
                     end) (seq 0 (Nat.max (tlen ts1 - cl) (tlen tsA - ct))).

(** A segment with the targets of some inputs replaced by variables. *)
Definition sreplace (prs : list ((lexp * nat) * (lexp * nat))) (s : seg) : option seg :=
  fold_right (fun g acc => obind acc (fun sg =>
    match entry_of s g with
    | Some (ts, m) =>
        let mine := filter (fun pq => lexp_eqb (fst (fst pq)) g) prs in
        let n := fold_right (fun pq acc => Nat.max (S (snd (fst pq))) acc) (List.length ts) mine in
        let tsx := map (fun j => match find (fun pq => Nat.eqb (snd (fst pq)) j) mine with
                                 | Some pq => NVar (fst (snd pq)) (snd (snd pq))
                                 | None => match seg_tgt F s g j with Some x => x | None => NVar g j end
                                 end) (seq 0 n) in
        sset F g (tl_of tsx) (m + (n - List.length ts)) sg
    | None => None
    end)) (Some s) (nodup_l (map (fun pq => fst (fst pq)) prs) []).

(** Two segments that the word [K] after them cannot tell apart: the
    same targets, or variables with the same key. *)
Definition seg_keq (K : lword) (s s' : seg) : bool :=
  forallb (fun g =>
    match entry_of s g, entry_of s' g with
    | Some (ts, m), Some (ts', m') =>
        Nat.eqb (m + List.length ts') (m' + List.length ts)
        && forallb (fun j => match seg_tgt F s g j, seg_tgt F s' g j with
                             | Some x, Some y =>
                                 ntgt_eqb x y
                                 || match x, y with
                                    | NVar g1 i1, NVar g2 i2 => okey_eqb (vfollow F K g1 i1) (vfollow F K g2 i2)
                                    | _, _ => false
                                    end
                             | _, _ => false
                             end) (seq 0 (Nat.max (List.length ts) (List.length ts')))
    | _, _ => false
    end) (nodup_l (LNone :: seg_labels s ++ seg_labels s') []).

Fixpoint xoff (LT : list (lexp * nat)) (g : lexp) : nat :=
  match LT with [] => 0 | (h, n) :: r => if lexp_eqb h g then 0 else n + xoff r g end.

Definition hopg (L : list (lexp * nat)) (a : nat) (Sp Sg S1 : seg)
  : option (seg * list (lexp * nat) * seg * list ntgt) :=
  match find (hop_cand a) (stargets Sp) with
  | Some (NBind u (WAtom A LT _ w') b) =>
      let T := NBind u (WAtom A LT a w') b in
      let labs := fold_right (linsert F) (linsert F LNone (wlabs F [LS Sg; LS S1])) (map fst L ++ map fst LT) in
      if forallb (fun g => match g with LNone => bthrough Sg L LT A | _ => through_ok Sg L LT g end) labs then
        let X := flat_map (fun '(g, n) => map (fun j => match g with
                                                       | LNone => match seg_tgt F A LNone j with Some x => x | None => NVar LNone j end
                                                       | _ => NVar g j end) (seq 0 n)) LT in
        let n := List.length X in
        let Jof := fun g => match entry_of Sg g with
                            | Some (ts, _) => filter (fun j => match nth_error ts j with Some t => ntgt_eqb t T | None => false end)
                                                     (seq 0 (List.length ts))
                            | None => [] end in
        if forallb (fun g => forallb (fun j => j <? lcn F L g) (Jof g)) labs
           && negb (forallb (fun g => match Jof g with [] => true | _ => false end) labs) then
          let extra := fun g => match g with LNone => n | _ => 0 end in
          let L2of := fun g => lcn F L g - List.length (Jof g) + extra g in
          let pi := mkseg F (map (fun g =>
                      let ct := lcn F LT g in
                      (g, tl_of (map (fun j => NVar LNone (xoff LT g + j)) (seq 0 ct)),
                       L2of g)) labs) in
          match obind pi (fun p => wcomp F ntm (WEnd p) w') with
          | Some w2 =>
              let T2 := NBind u (match b, w2 with None, WEnd Nx => WEnd (sdrop_none Nx) | _, _ => w2 end) b in
              let e0 := mkseg F (map (fun g =>
                          let J := Jof g in
                          let cl := lcn F L g in
                          (g, tl_of (map (fun j => if mem j J then T2
                                                   else NVar g (extra g + j - List.length (filter (fun j' => j' <? j) J))) (seq 0 cl)),
                           extra g + cl - List.length J)) labs) in
              let S1r := fold_right (fun g acc => obind acc (fun sg =>
                           match Jof g, entry_of S1 g with
                           | [], _ => Some sg
                           | J, Some (ts, m) =>
                               let nn := Nat.max (List.length ts) (lcn F L g) in
                               let tsx := map (fun j => match seg_tgt F S1 g j with Some x => x | None => NVar g j end) (seq 0 nn) in
                               sset F g (tl_of (remove_ix J tsx 0)) (m + (nn - List.length ts)) sg
                           | _, None => None end)) (Some S1) labs in
              let L2 := filter (fun p => negb (Nat.eqb (snd p) 0)) (map (fun g => (g, L2of g)) labs) in
              match e0, S1r with
              | Some e, Some sb => Some (e, L2, sb, X)
              | _, _ => None
              end
          | None => None
          end
        else None
      else None
  | _ => None
  end.

(** The term is in the [p]-th segment after the atom. *)
(** The term is in the [p]-th segment after the atom.  The targets of
    that segment first become the variables the payload's atom gives
    (the rest of the word cannot tell, [seg_keq]); then the two words
    are the same, which is checked by composing them. *)
Definition comp (l : list seg) : option seg :=
  match l with
  | [] => None
  | x :: r => fold_left (fun acc s => obind acc (fun g => fcomp F ntm s g)) r (Some x)
  end.

Definition segs_of (l : lword) : list seg := flat_map (fun x => match x with LS s => [s] | _ => [] end) l.

Definition hop_at (L : list (lexp * nat)) (a : nat) (p : nat) (K : lword) : option (seg * list (lexp * nat) * lword) :=
  let segs := segs_of (firstn p K) in
  let K2 := skipn p K in
  if negb (Nat.eqb (List.length segs) p) then None else
  match rev segs with
  | Sp :: rpre =>
      match find (hop_cand a) (stargets Sp), comp segs with
      | Some (NBind u (WAtom A LT _ w') b), Some Sg0 =>
          let labs := fold_right (linsert F) (linsert F LNone (wlabs F [LS Sg0])) (map fst L ++ map fst LT) in
          let pairs := flat_map (fun g => match g with LNone => bpairs Sg0 L LT A | _ => npairs Sg0 L LT g end) labs in
          let pre := comp (rev rpre) in
          let pin := fun v : lexp * nat =>
            match pre with
            | None => Some v
            | Some sg => match seg_tgt F sg (fst v) (snd v) with Some (NVar g i) => Some (g, i) | _ => None end
            end in
          let prs := map (fun pq => (pin (fst pq), snd pq)) pairs in
          if forallb (fun pq => match fst pq with Some _ => true | None => false end) prs then
            let prs1 := flat_map (fun pq => match fst pq with Some u => [(u, snd pq)] | None => [] end) prs in
            let Spx := match prs1 with
                       | [] => Some Sp
                       | _ => if forallb (fun pq => forallb (fun rs => negb (veqb (fst pq) (fst rs)) || veqb (snd pq) (snd rs)) prs1) prs1
                              then match sreplace prs1 Sp with
                                   | Some x => if seg_keq K2 Sp x && sdistb F x then Some x else None
                                   | None => None
                                   end
                              else None
                       end in
            match Spx with
            | Some Sp1 =>
                let segs1 := rev (Sp1 :: rpre) in
                match segs1, comp segs1 with
                | S1 :: rest, Some Sg =>
                    match hopg L a Sp1 Sg S1 with
                    | Some (e0, L2, S1r, X) =>
                        let K1 := LS S1r :: map LS rest ++ K2 in
                        match (match X with [] => Some K1 | _ => thread p X K1 end) with
                        | Some Kx =>
                            let segsx := segs_of (firstn p Kx) in
                            match comp segsx with
                            | Some Sg' =>
                                match wcomp F ntm (WAtom Sg L a (WEnd SNil)) (WEnd SNil),
                                      wcomp F ntm (WAtom Sg' L2 a (WEnd SNil)) (WEnd e0) with
                                | Some w1, Some w2 =>
                                    if word_eqb w1 w2 && sdistb F e0 && forallb (sdistb F) segsx
                                       && lword_eqb Kx (map LS segsx ++ K2)
                                    then Some (e0, L2, Kx) else None
                                | _, _ => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | _, _ => None
                end
            | None => None
            end
          else None
      | _, _ => None
      end
  | [] => None
  end.

Fixpoint catom (fuel : nat) (cc : seg -> lword -> option lword) (L : list (lexp * nat)) (a : nat) (K : lword) : option lword :=
  match fuel with
  | 0 => Some (LA L a :: K)
  | S f =>
      let nseg := (fix cnt (l : lword) : nat := match l with LS _ :: r => S (cnt r) | _ => 0 end) K in
      match (fix try (ps : list nat) : option (nat * (seg * list (lexp * nat) * lword)) :=
               match ps with
               | [] => None
               | p :: r => match hop_at L a p K with Some x => Some (p, x) | None => try r end
               end) (seq 1 nseg) with
      | Some (p, (e0, L2, Kx)) =>
          obind (recons cc p Kx) (fun K3 => obind (catom f cc L2 a K3) (cc e0))
      | None => Some (LA L a :: K)
      end
  end.

Fixpoint canon_f (fuel : nat) (l : lword) : option lword :=
  match l with
  | [] => Some []
  | LS s :: r => obind (canon_f fuel r) (ccons fuel s)
  | LA L a :: r => obind (canon_f fuel r) (catom fuel (ccons fuel) L a)
  end.

Definition canon (l : lword) : option lword := canon_f (4 * List.length l + 100) l.

End Canonical.
