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
Fixpoint same_rest (sg : seg) (K : lword) : bool :=
  match sg with
  | SNil => true
  | SEnt g ts m r =>
      if Nat.eqb (tlen ts) m
         && forallb (fun j => match tnth ts j with
                              | NVar g' i' => okey_eqb (vfollow F K g' i') (vfollow F K g j)
                              | _ => false
                              end) (seq 0 (tlen ts))
      then same_rest r K else false
  end.

Fixpoint sapp (a b : seg) : seg := match a with SNil => b | SEnt h ts m r => SEnt h ts m (sapp r b) end.

(** The entries of [s] up to the label [g], and the others. *)
Fixpoint ssplit (g : lexp) (s : seg) : seg * seg :=
  match s with
  | SNil => (SNil, SNil)
  | SEnt h ts m r => match lcmp F g h with
                     | Some Lt => (SNil, s)
                     | _ => let '(a, b) := ssplit g r in (SEnt h ts m a, b)
                     end
  end.

Fixpoint slast (s : seg) : option lexp :=
  match s with SNil => None | SEnt h _ _ r => match slast r with Some x => Some x | None => Some h end end.

Definition lt_first (g : option lexp) (s : seg) : bool :=
  match g, s with
  | Some g, SEnt h _ _ _ => match lcmp F g h with Some Lt => true | _ => false end
  | _, _ => true
  end.

(** Every named variable goes to a variable with its own label. *)
Fixpoint diagb (s : seg) : bool :=
  match s with
  | SNil => true
  | SEnt g ts _ r =>
      negb (lexp_eqb g LNone)
      && forallb (fun t => match t with NVar g' _ => lexp_eqb g' g | _ => false end) (tl_list ts)
      && diagb r
  end.

(** What [sig] followed by [s1] does to named variables.  While [sig]
    keeps the label of every variable ([dg]), only its entries up to the
    last label of [s1] are composed, and the others are kept as they
    are. *)
Definition sstep (dg : bool) (s1 sig : seg) : option (bool * seg) :=
  let slow := fun _ : unit => option_map (fun c => (false, sdrop_none c)) (fcomp F ntm s1 sig) in
  if dg then
    let s1n := sdrop_none s1 in
    match slast s1n with
    | None => Some (true, sig)
    | Some g =>
        if sortb F s1n then
          let '(pre, post) := ssplit g sig in
          match fcomp F ntm s1n pre with
          | Some c => if sortb F c && lt_first (slast c) post then Some (diagb c, sapp c post) else slow tt
          | None => slow tt
          end
        else slow tt
    end
  else slow tt.

(** [sig] is what the segments passed so far do to named variables; the
    segment found is the last one whose rest cannot tell it from the
    identity. *)
Fixpoint scan (dg : bool) (sig : seg) (K : lword) (j : nat) : option nat :=
  match K with
  | LS s1 :: K' =>
      match sstep dg s1 sig with
      | Some (dg', sg) =>
          if (if dg' then false else has_terms sg) then None
          else if same_rest sg K' then (match scan dg' sg K' (S j) with Some j' => Some j' | None => Some (S j) end)
          else scan dg' sg K' (S j)
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

(** An input of [s] with the target [t]. *)
Definition src_of (s : seg) (t : ntgt) : option (lexp * nat) :=
  match vmin F (named_srcs F s t) with
  | Some w => Some w
  | None =>
      match findix t (fst (bent F s)) 0 with
      | k :: _ => Some (LNone, k)
      | [] => match t with
              | NVar LNone k => let '(ts, m) := bent F s in if m <=? k then Some (LNone, k - m + tlen ts) else None
              | _ => None
              end
      end
  end.

(** A variable in front of [K] that goes to the target [t] of its
    [j]-th segment. *)
Fixpoint trace (K : lword) (j : nat) (t : ntgt) : option (lexp * nat) :=
  match j, K with
  | 1, LS s :: _ => src_of s t
  | S j', LS s :: K' => obind (trace K' j' t) (fun w => src_of s (NVar (fst w) (snd w)))
  | _, _ => None
  end.

(** The terms of [s] joining the [j]-th segment of [K] = [s1 :: K'],
    when that segment has them already: the variables after [s1] that go
    to them. *)
Definition shared (j : nat) (T : list ntgt) (s1 : seg) (K' : lword) : option (list ntgt) :=
  omapl (fun t =>
    match tsh_chain j t (LS s1 :: K') with
    | Some t' =>
        match trace K' (j - 1) t' with
        | Some v =>
            match lfollow K' (fst v) (snd v) with
            | Some (FT x d) =>
                if ntgt_eqb x t' && Nat.eqb (d + j) (S (List.length K')) then Some (NVar (fst v) (snd v)) else None
            | _ => None
            end
        | None => None
        end
    | None => None
    end) T.

(** How a segment joins a later one: its terms are there already and
    [c] replaces the first segment; or they are carried there, [Kp]
    being the word with them; or only some can be carried, the segment
    [em], and the others stay in [se]. *)
Inductive jres := JShare (c : seg) | JThread (j : nat) (sa : seg) (Kp : lword) | JPart (se em : seg).

Definition try_join (s s1 : seg) (K' : lword) : option jres :=
  let K := LS s1 :: K' in
  if named_term s1 then None
  else match scan true SNil K 0 with
       | Some j =>
           if match skipn (j - 1) K with
              | LS sj :: Kj1 => if has_terms sj then true else above (LS sj :: Kj1) Kj1
              | _ => false
              end then
           obind (unterm s) (fun '(sa, T) =>
             if forallb settled T then
               match obind (shared j T s1 K') (fun V => obind (tfront F V s1) (fun X => fcomp F ntm X sa)) with
               | Some c => Some (JShare c)
               | None =>
               let mv := map (fun t => match tsh_chain j t K with Some _ => true | None => false end) T in
               if forallb (fun b => b) mv then obind (thread j T K) (fun Kp => Some (JThread j sa Kp))
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
                             if seg_eqb c eT && sdistb F e && sdistb F em && sdistb F se then Some (JPart se em) else None
                         | _, _ => None
                         end
                     | _, _, _ => None
                     end
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
            match try_join s s1 K' with
            | Some (JShare c) => cc0 c K'
            | Some (JPart se em) => obind (ccons f em K) (ccons f se)
            | Some (JThread j sa Kp) =>
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


Definition hop_cand (a : nat) (t : ntgt) : bool :=
  match t with
  | NBind u (WAtom A _ a' _) _ => Nat.eqb a a' && (u <? ntm) && match sdrop_none A with SNil => true | _ => false end
  | _ => false
  end.

Definition otgt_eqb (x y : option ntgt) : bool :=
  match x, y with Some p, Some q => ntgt_eqb p q | _, _ => false end.

(** After the atom on the line, what the atom gives out goes on as it
    does after the atom of the payload, whose tail is [A]. *)
Definition thr (Sg : seg) (L LT : list (lexp * nat)) (A : seg) (g : lexp) : bool :=
  let cl := lcn F L g in
  let ct := lcn F LT g in
  match entry_of Sg g, entry_of A g with
  | Some (ts1, m1), Some (tsA, mA) =>
      Nat.eqb (m1 + cl + List.length tsA) (mA + ct + List.length ts1)
      && forallb (fun k => otgt_eqb (seg_tgt F Sg g (k + cl)) (seg_tgt F A g (k + ct)))
                 (seq 0 (Nat.max (List.length ts1 - cl) (List.length tsA - ct)))
  | _, _ => false
  end.

(** The tail that makes it so: what [A] does to the variables the atom
    of the payload passes around, and what [Sg] does to the others. *)
Definition line_tail (Sg : seg) (L LT : list (lexp * nat)) (A : seg) (labs : list lexp) : option seg :=
  obind (omapl (fun g =>
           let cl := lcn F L g in
           let ct := lcn F LT g in
           match entry_of Sg g with
           | Some (tsS, mS) =>
               let nS := List.length tsS in
               option_map (fun l => (g, tl_of l, mS + (cl - nS)))
                 (omapl (fun x => match x with Some (NVar h i) => Some (NVar h i) | _ => None end)
                        (map (seg_tgt F A g) (seq 0 ct) ++ map (seg_tgt F Sg g) (seq cl (nS - cl))))
           | None => None
           end) labs) (mkseg F).

(** A segment with the term [T] replaced by [T']. *)
Definition trepl (T T' : ntgt) (s : seg) : option seg :=
  mkseg F (map (fun '(g, ts, m) => (g, tl_of (map (fun x => if ntgt_eqb x T then T' else x) (tl_list ts)), m)) (ents s)).

(** Two segments that the word [K] after them cannot tell apart: the
    same targets, or variables with the same key, or terms that [tk]
    accepts. *)
Definition seg_keqx (tk : ntgt -> ntgt -> bool) (K : lword) (s s' : seg) : bool :=
  forallb (fun g =>
    match entry_of s g, entry_of s' g with
    | Some (ts, m), Some (ts', m') =>
        Nat.eqb (m + List.length ts') (m' + List.length ts)
        && forallb (fun j => match seg_tgt F s g j, seg_tgt F s' g j with
                             | Some x, Some y =>
                                 ntgt_eqb x y
                                 || match x, y with
                                    | NVar g1 i1, NVar g2 i2 => okey_eqb (vfollow F K g1 i1) (vfollow F K g2 i2)
                                    | NBind _ _ _, NBind _ _ _ => tk x y
                                    | _, _ => false
                                    end
                             | _, _ => false
                             end) (seq 0 (Nat.max (List.length ts) (List.length ts')))
    | _, _ => false
    end) (nodup_l (LNone :: seg_labels s ++ seg_labels s') []).

Definition seg_keq0 := seg_keqx (fun _ _ => false).

(** The same term, with tails that [K] cannot tell apart. *)
Definition tkeq (K : lword) (x y : ntgt) : bool :=
  match x, ttail x, ttail y with
  | NBind u _ _, Some A, Some A' => (u <? ntm) && ntgt_eqb (tset x A') y && seg_keq0 K A A'
  | _, _, _ => false
  end.

Definition seg_keq (K : lword) := seg_keqx (tkeq K) K.

Fixpoint xoff (LT : list (lexp * nat)) (g : lexp) : nat :=
  match LT with [] => 0 | (h, n) :: r => if lexp_eqb h g then 0 else n + xoff r g end.

Definition hopg (L : list (lexp * nat)) (a u : nat) (A : seg) (LT : list (lexp * nat)) (w' : word) (b : option nat)
    (T : ntgt) (Sg S1 : seg) : option (seg * list (lexp * nat) * seg * list ntgt) :=
  let labs := fold_right (linsert F) (linsert F LNone (wlabs F [LS Sg; LS S1; LS A])) (map fst L ++ map fst LT) in
  if forallb (thr Sg L LT A) labs then
    let X := flat_map (fun '(g, n) => map (fun j => match seg_tgt F A g j with Some x => x | None => NVar g j end)
                                          (seq 0 n)) LT in
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
  else None.

(** The term is in the [p]-th segment after the atom. *)
(** The term is in the [p]-th segment after the atom.  The targets of
    tail of the term first becomes what the segments do to the
    variables the atom gives (the rest of the word cannot tell,
    [seg_keq]); then the two words are the same, which is checked by
    composing them. *)
Definition comp (l : list seg) : option seg :=
  match l with
  | [] => None
  | x :: r => fold_left (fun acc s => obind acc (fun g => fcomp F ntm s g)) r (Some x)
  end.

Definition segs_of (l : lword) : list seg := flat_map (fun x => match x with LS s => [s] | _ => [] end) l.

Definition hop_prop (L : list (lexp * nat)) (a : nat) (p : nat) (K : lword) (T0 : ntgt)
  : option (seg * seg * list (lexp * nat) * lword) :=
  let segs := segs_of (firstn p K) in
  let K2 := skipn p K in
  if negb (Nat.eqb (List.length segs) p) then None else
  match rev segs, segs with
  | Sp :: rpre, S1 :: rest =>
      match T0, comp segs with
      | NBind u (WAtom A LT _ w') b, Some Sg0 =>
          let T := NBind u (WAtom A LT a w') b in
          let labs := fold_right (linsert F) (linsert F LNone (wlabs F [LS Sg0])) (map fst L ++ map fst LT) in
          match line_tail Sg0 L LT A labs with
          | Some A' =>
              let T' := tset T A' in
              match (if seg_eqb A A' then Some Sp else trepl T T' Sp) with
              | Some Sp1 =>
                  if seg_eqb Sp Sp1 || (seg_keq K2 Sp Sp1 && sdistb F Sp1) then
                    match comp (rev (Sp1 :: rpre)) with
                    | Some Sg =>
                        match hopg L a u A' LT w' b T' Sg S1 with
                        | Some (e0, L2, S1r, X) =>
                            let K1 := LS S1r :: map LS rest ++ K2 in
                            match (match X with [] => Some K1 | _ => thread p X K1 end) with
                            | Some Kx => Some (Sp1, e0, L2, Kx)
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                  else None
              | None => None
              end
          | None => None
          end
      | _, _ => None
      end
  | _, _ => None
  end.

(** The proposal is checked: the last segment may have changed to one
    the rest cannot tell from it, and the two words compose to the same. *)
Definition hop_chk (L : list (lexp * nat)) (a p : nat) (K : lword) (Sp1 e0 : seg) (L2 : list (lexp * nat)) (Kx : lword) : bool :=
  let segs := segs_of (firstn p K) in
  let K2 := skipn p K in
  Nat.eqb (List.length segs) p
  && match rev segs with
     | Sp :: rpre =>
         (seg_eqb Sp Sp1 || (seg_keq K2 Sp Sp1 && sdistb F Sp1))
         && let segsx := segs_of (firstn p Kx) in
            match comp (rev (Sp1 :: rpre)), comp segsx with
            | Some Sg, Some Sg' =>
                match wcomp F ntm (WAtom Sg L a (WEnd SNil)) (WEnd SNil),
                      wcomp F ntm (WAtom Sg' L2 a (WEnd SNil)) (WEnd e0) with
                | Some w1, Some w2 =>
                    word_eqb w1 w2 && sdistb F e0 && forallb (sdistb F) segsx && lword_eqb Kx (map LS segsx ++ K2)
                | _, _ => false
                end
            | _, _ => false
            end
     | [] => false
     end.

Definition hop_try (L : list (lexp * nat)) (a : nat) (p : nat) (K : lword) (T0 : ntgt)
  : option (seg * list (lexp * nat) * lword) :=
  match hop_prop L a p K T0 with
  | Some (Sp1, e0, L2, Kx) => if hop_chk L a p K Sp1 e0 L2 Kx then Some (e0, L2, Kx) else None
  | None => None
  end.

Fixpoint first_some {A B} (f : A -> option B) (l : list A) : option B :=
  match l with
  | [] => None
  | x :: r => match f x with Some y => Some y | None => first_some f r end
  end.

(** The first term of the [p]-th segment that can go in front of the
    atom. *)
Definition hop_at (L : list (lexp * nat)) (a : nat) (p : nat) (K : lword) : option (seg * list (lexp * nat) * lword) :=
  match rev (segs_of (firstn p K)) with
  | Sp :: _ => first_some (hop_try L a p K) (filter (hop_cand a) (stargets Sp))
  | [] => None
  end.

Fixpoint nlead (l : lword) : nat := match l with LS _ :: r => S (nlead r) | _ => 0 end.

Fixpoint hop_first (L : list (lexp * nat)) (a : nat) (K : lword) (ps : list nat)
  : option (nat * (seg * list (lexp * nat) * lword)) :=
  match ps with
  | [] => None
  | p :: r => match hop_at L a p K with Some x => Some (p, x) | None => hop_first L a K r end
  end.

Fixpoint catom (fuel : nat) (cc : seg -> lword -> option lword) (L : list (lexp * nat)) (a : nat) (K : lword) : option lword :=
  match fuel with
  | 0 => Some (LA L a :: K)
  | S f =>
      match hop_first L a K (seq 1 (nlead K)) with
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

(** ** Soundness *)

Section Sound.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.
Hypothesis Hntm : ntm <= List.length tenv.

Local Notation lden := (lden lenv).
Local Notation tden := (tden lenv tenv aenv penv).
Local Notation sden := (sden lenv tenv aenv penv).
Local Notation wden := (wden lenv tenv aenv penv).
Local Notation sget := (sget lenv).
Local Notation sdistd := (sdistd lenv).
Local Notation tdist := (tdist lenv).
Local Notation tldist := (tldist lenv).
Local Notation wdist := (wdist lenv).
Local Notation lwden := (lwden lenv tenv aenv penv).
Local Notation lwdist := (lwdist lenv).
Local Notation esem := (esem lenv tenv aenv penv).

Lemma iface_sound s K s' io : sdistd s -> lwdist K -> iface F ntm s K = (s', io) ->
  sdistd s' /\ sdistd io /\ rcompose (lwden K) (rcompose (sden io) (sden s')) = rcompose (lwden K) (sden s).
Proof.
  intros Hs HK; unfold iface.
  set (sa := match reroute_g F ntm s K with Some x => x | None => s end).
  assert (Ha : sdistd sa /\ rcompose (lwden K) (sden sa) = rcompose (lwden K) (sden s)).
  { unfold sa; destruct (reroute_g F ntm s K) as [x|] eqn:E; [|split; [exact Hs|reflexivity]].
    exact (reroute_g_sound lenv tenv aenv penv F HF ntm Hntm s K x Hs HK E). }
  destruct Ha as [Hsa Da].
  destruct (renum F ntm _ _ sa) as [[x y]|] eqn:E.
  - intros H; injection H as <- <-.
    destruct (renum_sound lenv tenv aenv penv F HF ntm Hntm _ _ sa x y Hsa E) as [Hx [Hy D]].
    split; [exact Hx|split; [exact Hy|]]; rewrite D; exact Da.
  - intros H; injection H as <- <-; split; [exact Hsa|split; [exact I|]].
    change (sden SNil) with (@ridentity T); rewrite rcompose_identity_l; exact Da.
Qed.

Lemma sget_ents l s : forall ts m, sget l s = Some (ts, m) -> exists g, In (g, ts, m) (ents s) /\ lden g = l.
Proof.
  induction s as [|h ts0 m0 r IH] using seg_spine; intros ts m; cbn [Normalise.sget ents]; [discriminate|].
  destruct (label_eqb_spec (lden h) l) as [E|E].
  - intros H; injection H as <- <-; exists h; split; [left; reflexivity|exact E].
  - intros H; destruct (IH ts m H) as [g [H1 H2]]; exists g; split; [right; exact H1|exact H2].
Qed.

Lemma same_rest_ents sg K : same_rest F sg K = true -> forall g ts m, In (g, ts, m) (ents sg) ->
  Nat.eqb (tlen ts) m
  && forallb (fun j => match tnth ts j with
                       | NVar g' i' => okey_eqb (vfollow F K g' i') (vfollow F K g j)
                       | _ => false
                       end) (seq 0 (tlen ts)) = true.
Proof.
  induction sg as [|h ts0 m0 r IH] using seg_spine; cbn [same_rest ents]; [intros _ g ts m []|].
  match goal with |- (if ?X then _ else _) = true -> _ => destruct X eqn:E end; [|discriminate].
  intros H g ts m [Heq|Hin]; [injection Heq as <- <- <-; exact E|exact (IH H g ts m Hin)].
Qed.

Lemma same_rest_sound sg K v : sdistd sg -> lwdist K -> same_rest F sg K = true -> v_label v <> None ->
  cres (lwden K) (rapply (sden sg) v) = rapply (lwden K) v.
Proof.
  intros Hsg HK H Hv.
  rewrite (rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; exact Hsg).
  destruct v as [l j]; cbn [v_label v_index] in *.
  destruct (sget l sg) as [[ts m]|] eqn:Eg; [|reflexivity].
  destruct (sget_ents l _ ts m Eg) as [g [Hin Hl]]; subst l.
  pose proof (same_rest_ents sg K H g ts m Hin) as H'; clear H; rename H' into H.
  apply andb_true_iff in H as [H1 H2]; apply Nat.eqb_eq in H1; rewrite forallb_forall in H2.
  unfold Normalise.esem; destruct (Nat.ltb_spec j (tlen ts)) as [Hj|Hj].
  - specialize (H2 j (proj2 (in_seq _ _ _) (conj (Nat.le_0_l _) Hj))).
    destruct (tnth ts j) as [g' i'|? ? ?]; [|discriminate].
    apply okey_eqb_eq in H2 as [k [E1 E2]]; cbn [Normalise.tden rtarget_result cres].
    exact (vfollow_sound lenv tenv aenv penv F HF ntm Hntm K HK _ _ _ _ k E1 E2).
  - cbn [cres]; do 2 f_equal; lia.
Qed.

(** *** One step of the scan *)

Local Notation sorted := (sorted lenv).
Local Notation below := (below lenv).

Definition lpres (s : seg) : Prop :=
  forall l i, l <> None -> exists k, esem l (sget l s) i = inl (mk_rvar l k).

Lemma sget_sapp l a b : sget l (sapp a b) = match sget l a with Some e => Some e | None => sget l b end.
Proof.
  induction a as [|h ts m r IH] using seg_spine; cbn [sapp Normalise.sget]; [reflexivity|].
  destruct (label_eqb (lden h) l); [reflexivity|exact IH].
Qed.

Lemma ssplit_app g s : forall a b, ssplit F g s = (a, b) -> s = sapp a b /\ lt_first F (Some g) b = true.
Proof.
  induction s as [|h ts m r IH] using seg_spine; intros a b; cbn [ssplit].
  - intros H; injection H as <- <-; split; reflexivity.
  - destruct (ssplit F g r) as [a' b'] eqn:E; destruct (IH a' b' eq_refl) as [E1 E2].
    destruct (lcmp F g h) as [[| |]|] eqn:Ec; intros H; injection H as <- <-; cbn [sapp];
      try (split; [f_equal; exact E1|exact E2]).
    split; [reflexivity|cbn [lt_first]; rewrite Ec; reflexivity].
Qed.

Lemma sdistd_sapp a b : sdistd (sapp a b) -> sdistd a /\ sdistd b.
Proof.
  induction a as [|h ts m r IH] using seg_spine; cbn [sapp]; [intros H; split; [exact I|exact H]|].
  intros [Hn [Ht Hd]]; destruct (IH Hd) as [A B]; split; [|exact B].
  split; [|split; [exact Ht|exact A]].
  rewrite sget_sapp in Hn; destruct (sget (lden h) r); [discriminate|reflexivity].
Qed.

Lemma sapp_dist_disj a b : sdistd (sapp a b) -> forall l e, sget l b = Some e -> sget l a = None.
Proof.
  induction a as [|h ts m r IH] using seg_spine; cbn [sapp]; [reflexivity|].
  intros [Hn [_ Hd]] l e He; cbn [Normalise.sget]; rewrite sget_sapp in Hn.
  destruct (label_eqb_spec (lden h) l) as [<-|]; [|exact (IH Hd l e He)].
  destruct (sget (lden h) r); [discriminate|]; rewrite He in Hn; discriminate.
Qed.

Lemma sorted_sapp_r a b : sorted (sapp a b) -> sorted b.
Proof.
  induction a as [|h ts m r IH] using seg_spine; cbn [sapp]; [exact (fun H => H)|intros [_ H]; exact (IH H)].
Qed.

Lemma below_sget b s l e : below b s -> sget l s = Some e -> olabel_lt b l.
Proof.
  induction s as [|h ts m r IH] using seg_spine; cbn [Normalise.sget]; [discriminate|]; intros [H1 H2].
  destruct (label_eqb_spec (lden h) l) as [<-|]; [intros _; exact H1|exact (IH H2)].
Qed.

Lemma slast_none s : slast s = None -> s = SNil.
Proof. destruct s as [|h ts m r]; [reflexivity|]; cbn [slast]; destruct (slast r); discriminate. Qed.

Lemma below_slast b s : forall h, below b s -> slast s = Some h -> olabel_lt b (lden h).
Proof.
  induction s as [|g ts m r IH] using seg_spine; intros h; cbn [slast]; [discriminate|]; intros [H1 H2].
  destruct (slast r) as [x|] eqn:Er; intros H; injection H as <-; [exact (IH _ H2 eq_refl)|exact H1].
Qed.

Lemma slast_upper s : forall h, sorted s -> slast s = Some h ->
  forall l e, sget l s = Some e -> l = lden h \/ olabel_lt l (lden h).
Proof.
  induction s as [|g ts m r IH] using seg_spine; intros h; cbn [slast]; [discriminate|]; intros [Hb Hs].
  destruct (slast r) as [x|] eqn:Er; intros H; injection H as <-; intros l e; cbn [Normalise.sget].
  - destruct (label_eqb_spec (lden g) l) as [<-|]; [intros _; right; exact (below_slast _ _ _ Hb Er)|exact (IH _ Hs eq_refl l e)].
  - rewrite (slast_none r Er); cbn [Normalise.sget].
    destruct (label_eqb_spec (lden g) l) as [<-|]; [intros _; left; reflexivity|discriminate].
Qed.

Lemma lt_first_sound g b : lt_first F (Some g) b = true -> sorted b ->
  forall l e, sget l b = Some e -> olabel_lt (lden g) l.
Proof.
  destruct b as [|p ts m r]; cbn [lt_first]; [intros _ _ l e; discriminate|].
  destruct (lcmp F g p) as [[| |]|] eqn:E; try discriminate; intros _ [Hb _] l e.
  pose proof (lcmp_sound lenv F HF _ _ _ E) as Hlt; cbn in Hlt; cbn [Normalise.sget].
  destruct (label_eqb_spec (lden p) l) as [<-|]; [intros _; exact Hlt|].
  intros H; exact (olabel_lt_trans _ _ _ Hlt (below_sget _ _ _ _ Hb H)).
Qed.

Lemma sapp_disj X post : sorted X -> lt_first F (slast X) post = true -> sorted post ->
  forall l e, sget l post = Some e -> sget l X = None.
Proof.
  intros HX Hlt Hp l e He; destruct (slast X) as [h|] eqn:El; [|rewrite (slast_none X El); reflexivity].
  pose proof (lt_first_sound h post Hlt Hp l e He) as H1.
  destruct (sget l X) as [e'|] eqn:Ex; [|reflexivity]; exfalso.
  destruct (slast_upper X h HX El l e' Ex) as [->|H2];
    [exact (olabel_lt_irrefl _ H1)|exact (olabel_lt_irrefl _ (olabel_lt_trans _ _ _ H1 H2))].
Qed.

Lemma sdistd_sapp_i a b : sdistd a -> sdistd b -> (forall l e, sget l b = Some e -> sget l a = None) ->
  sdistd (sapp a b).
Proof.
  induction a as [|h ts m r IH] using seg_spine; cbn [sapp]; [intros _ H _; exact H|].
  intros [Hn [Ht Hd]] Hb Hdis; split; [|split; [exact Ht|]].
  - rewrite sget_sapp, Hn; destruct (sget (lden h) b) as [e|] eqn:E; [|reflexivity].
    specialize (Hdis _ _ E); cbn [Normalise.sget] in Hdis; rewrite label_eqb_refl in Hdis; discriminate.
  - apply IH; [exact Hd|exact Hb|]; intros l e E; specialize (Hdis l e E); cbn [Normalise.sget] in Hdis.
    destruct (label_eqb (lden h) l); [discriminate|exact Hdis].
Qed.

Lemma below_sapp x a b : below x a -> below x b -> below x (sapp a b).
Proof.
  induction a as [|h ts m r IH] using seg_spine; cbn [sapp]; [intros _ H; exact H|].
  intros [H1 H2] H; split; [exact H1|exact (IH H2 H)].
Qed.

Lemma sorted_sapp a b : sorted a -> sorted b -> lt_first F (slast a) b = true -> sorted (sapp a b).
Proof.
  induction a as [|g ts m r IH] using seg_spine; cbn [sapp]; [intros _ H _; exact H|].
  intros [Hb Hs] Hsb; cbn [slast]; intros Hlt.
  assert (Hgb : below (lden g) b).
  { destruct b as [|p tsp mp rp]; [exact I|].
    assert (Hgp : olabel_lt (lden g) (lden p)).
    { destruct (slast r) as [x|] eqn:Er; cbn [lt_first] in Hlt;
        match type of Hlt with context [lcmp F ?a p] => destruct (lcmp F a p) as [[| |]|] eqn:E end; try discriminate;
        pose proof (lcmp_sound lenv F HF _ _ _ E) as H1; cbn in H1;
        [exact (olabel_lt_trans _ _ _ (below_slast _ _ _ Hb Er) H1)|exact H1]. }
    split; [exact Hgp|exact (below_trans lenv _ _ _ Hgp (proj1 Hsb))]. }
  split; [exact (below_sapp _ _ _ Hb Hgb)|].
  destruct (slast r) as [x|] eqn:Er; [exact (IH Hs Hsb Hlt)|rewrite (slast_none r Er); exact Hsb].
Qed.

Lemma diagb_lpres s : diagb s = true -> lpres s.
Proof.
  intros H l i Hl; destruct (sget l s) as [[ts m]|] eqn:Eg; [|exists i; reflexivity].
  destruct (sget_ents l s ts m Eg) as [g [Hin Hg]]; subst l.
  assert (Hts : forall t, In t (tl_list ts) -> exists i', t = NVar g i').
  { clear Eg Hl; induction s as [|h ts0 m0 r IH] using seg_spine; [destruct Hin|]; cbn [diagb] in H; cbn [ents] in Hin.
    apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [_ H2].
    destruct Hin as [Heq|Hin]; [injection Heq as <- <- <-|exact (IH H3 Hin)].
    intros t Ht; rewrite forallb_forall in H2; specialize (H2 t Ht).
    destruct t as [g' i'|? ? ?]; [|discriminate]; apply lexp_eqb_eq in H2; subst g'; exists i'; reflexivity. }
  unfold Normalise.esem; destruct (Nat.ltb_spec i (tlen ts)) as [Hi|Hi]; [|eexists; reflexivity].
  destruct (Hts (tnth ts i)) as [i' E]; [rewrite tnth_list; apply nth_In; rewrite <- tlen_list; exact Hi|].
  rewrite E; exists i'; reflexivity.
Qed.

Lemma lpres_nil : lpres SNil.
Proof. intros l i _; exists i; reflexivity. Qed.

Lemma sstep_sound dg s1 sig dg' sg : sdistd s1 -> sdistd sig -> (dg = true -> sorted sig /\ lpres sig) ->
  sstep F ntm dg s1 sig = Some (dg', sg) ->
  sdistd sg /\ (dg' = true -> sorted sg /\ lpres sg)
  /\ forall w, v_label w <> None -> rapply (sden sg) w = cres (sden s1) (rapply (sden sig) w).
Proof.
  intros Hs1 Hsig Hinv; unfold sstep; cbv beta zeta.
  assert (Hslow : option_map (fun c => (false, sdrop_none c)) (fcomp F ntm s1 sig) = Some (dg', sg) ->
            sdistd sg /\ (dg' = true -> sorted sg /\ lpres sg)
            /\ forall w, v_label w <> None -> rapply (sden sg) w = cres (sden s1) (rapply (sden sig) w)).
  { destruct (fcomp F ntm s1 sig) as [c|] eqn:Ec; [|discriminate]; cbn [option_map]; intros H; injection H as <- <-.
    destruct (fcomp_sound lenv tenv aenv penv F HF ntm Hntm _ _ _ Hs1 Hsig Ec) as [Hc Dc].
    split; [exact (sdrop_dd lenv _ Hc)|split; [discriminate|]].
    intros w Hw; rewrite <- (named_sdrop_none lenv tenv aenv penv c w Hw), Dc; apply rapply_compose_cres. }
  destruct dg; [|exact Hslow]; destruct (Hinv eq_refl) as [Hso Hlp].
  pose proof (sdrop_dd lenv _ Hs1) as Hs1n.
  assert (Hnamed : forall l k, l <> None -> rapply (sden s1) (mk_rvar l k) = esem l (sget l (sdrop_none s1)) k).
  { intros l k Hl; rewrite (named_sdrop_none lenv tenv aenv penv s1 (mk_rvar l k) Hl).
    rewrite (rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; exact Hs1n); reflexivity. }
  destruct (slast (sdrop_none s1)) as [g|] eqn:El.
  2:{ intros H; injection H as <- <-; split; [exact Hsig|split; [intros _; exact (conj Hso Hlp)|]].
      intros [l i] Hw; cbn [v_label] in Hw.
      rewrite (rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; exact Hsig); cbn [v_label v_index].
      destruct (Hlp l i Hw) as [k Ek]; rewrite Ek; cbn [cres]; rewrite (Hnamed l k Hw), (slast_none _ El); reflexivity. }
  destruct (sortb F (sdrop_none s1)) eqn:Eso; [|exact Hslow].
  destruct (ssplit F g sig) as [pre post] eqn:Esp; destruct (ssplit_app g sig pre post Esp) as [Eapp Hgp].
  destruct (fcomp F ntm (sdrop_none s1) pre) as [c|] eqn:Ec; [|exact Hslow].
  destruct (sortb F c && lt_first F (slast c) post) eqn:Eb; [|exact Hslow].
  apply andb_true_iff in Eb as [Eb1 Eb2]; intros H; injection H as <- <-.
  clear Hslow; subst sig; destruct (sdistd_sapp pre post Hsig) as [Hpre Hpost].
  pose proof (sorted_sapp_r pre post Hso) as Hsp.
  destruct (fcomp_sound lenv tenv aenv penv F HF ntm Hntm _ _ _ Hs1n Hpre Ec) as [Hc Dc].
  pose proof (sortb_sound lenv F HF c Eb1) as Hcs; pose proof (sortb_sound lenv F HF _ Eso) as Hs1s.
  pose proof (sapp_disj c post Hcs Eb2 Hsp) as Hd1.
  assert (Hd2 : forall l e, sget l post = Some e -> sget l (sdrop_none s1) = None).
  { apply sapp_disj; [exact Hs1s|rewrite El; exact Hgp|exact Hsp]. }
  pose proof (sapp_dist_disj pre post Hsig) as Hd3.
  pose proof (sdistd_sapp_i c post Hc Hpost Hd1) as Hsg.
  assert (Hsem : forall l i, l <> None ->
            exists k, esem l (sget l (sapp pre post)) i = inl (mk_rvar l k)
                      /\ esem l (sget l (sapp c post)) i = rapply (sden s1) (mk_rvar l k)).
  { intros l i Hl; destruct (Hlp l i Hl) as [k Ek]; exists k; split; [exact Ek|].
    rewrite sget_sapp in Ek |- *; destruct (sget l post) as [e|] eqn:Ep.
    - rewrite (Hd1 l e Ep), (Hnamed l k Hl), (Hd2 l e Ep); rewrite (Hd3 l e Ep) in Ek; exact Ek.
    - assert (E1 : esem l (sget l c) i = rapply (sden s1) (mk_rvar l k)).
      { assert (R : rapply (sden c) (mk_rvar l i) = esem l (sget l c) i)
          by (rewrite (rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; exact Hc); reflexivity).
        rewrite <- R, Dc, rapply_compose_cres, (rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; exact Hpre).
        cbn [v_label v_index]; destruct (sget l pre) as [e|]; rewrite Ek; cbn [cres];
          symmetry; exact (named_sdrop_none lenv tenv aenv penv s1 (mk_rvar l k) Hl). }
      destruct (sget l c) as [e|]; exact E1. }
  split; [exact Hsg|split].
  - intros Hdg; split; [exact (sorted_sapp c post Hcs Hsp Eb2)|].
    intros l i Hl; rewrite sget_sapp; destruct (sget l c) as [e'|] eqn:Ecg.
    + pose proof (diagb_lpres c Hdg l i Hl) as Hx; rewrite Ecg in Hx; exact Hx.
    + destruct (sget l post) as [e|] eqn:Ep; [|exists i; reflexivity].
      pose proof (Hlp l i Hl) as Hx; rewrite sget_sapp, (Hd3 l e Ep), Ep in Hx; exact Hx.
  - intros [l i] Hw; cbn [v_label] in Hw.
    rewrite !(rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; assumption); cbn [v_label v_index].
    destruct (Hsem l i Hw) as [k [E1 E2]]; rewrite E1, E2; reflexivity.
Qed.

Lemma scan_ge K : forall dg sig j0 j, scan F ntm dg sig K j0 = Some j -> j0 < j.
Proof.
  induction K as [|[s1|L a] K IH]; intros dg sig j0 j; cbn [scan]; try discriminate.
  destruct (sstep F ntm dg s1 sig) as [[dg' sg]|]; [|discriminate].
  destruct (if dg' then false else has_terms sg); [discriminate|].
  destruct (same_rest F sg K).
  - destruct (scan F ntm dg' sg K (S j0)) as [j'|] eqn:E.
    + intros H; injection H as <-; apply IH in E; lia.
    + intros H; injection H as <-; lia.
  - intros H; apply IH in H; lia.
Qed.

Lemma scan_sound K : forall dg sig j0 j v, sdistd sig -> (dg = true -> sorted sig /\ lpres sig) -> lwdist K ->
  scan F ntm dg sig K j0 = Some j -> v_label v <> None ->
  cres (lwden K) (rapply (sden sig) v) = rapply (lwden (skipn (j - j0) K)) v.
Proof.
  induction K as [|[s1|L a] K IH]; intros dg sig j0 j v Hsig Hinv HK; cbn [scan]; try discriminate.
  inversion HK as [|? ? Hs1 HK']; subst.
  destruct (sstep F ntm dg s1 sig) as [[dg' sg]|] eqn:Est; [|discriminate].
  destruct (sstep_sound dg s1 sig dg' sg Hs1 Hsig Hinv Est) as [Hsg [Hinv' Hstep]].
  destruct (if dg' then false else has_terms sg); [discriminate|].
  assert (E0 : forall w, v_label w <> None ->
            cres (lwden (LS s1 :: K)) (rapply (sden sig) w) = cres (lwden K) (rapply (sden sg) w)).
  { intros w Hw; cbn [Layered.lwden]; rewrite <- cres_compose, (Hstep w Hw); reflexivity. }
  assert (Hrec : forall j', scan F ntm dg' sg K (S j0) = Some j' -> v_label v <> None ->
            cres (lwden (LS s1 :: K)) (rapply (sden sig) v) = rapply (lwden (skipn (j' - j0) (LS s1 :: K))) v).
  { intros j' H Hv; pose proof (scan_ge _ _ _ _ _ H) as Hj.
    rewrite (E0 v Hv), (IH _ _ _ _ v Hsg Hinv' HK' H Hv).
    replace (j' - j0) with (S (j' - S j0)) by lia; reflexivity. }
  destruct (same_rest F sg K) eqn:Es; [|exact (Hrec j)].
  destruct (scan F ntm dg' sg K (S j0)) as [j'|] eqn:E.
  - intros H; injection H as <-; exact (Hrec j' eq_refl).
  - intros H Hv; injection H as <-.
    replace (S j0 - j0) with 1 by lia; cbn [skipn]; rewrite (E0 v Hv).
    exact (same_rest_sound _ K v Hsg HK' Es Hv).
Qed.

(** *** Carrying a term *)

Lemma rapply_target_res (a : radj T) t : rtarget_result (rapply_target a t) = cres a (rtarget_result t).
Proof.
  destruct t as [w|u r]; cbn [rapply_target rtarget_result cres]; [|reflexivity].
  destruct (rapply a w) as [x|[y q]]; reflexivity.
Qed.

Lemma rtarget_result_inj (t t' : rtarget T) : rtarget_result t = rtarget_result t' -> t = t'.
Proof. destruct t, t'; cbn; intros H; inversion H; reflexivity. Qed.

Lemma settled_named A v : sdistd A -> settled_tail A = true -> v_label v <> None -> rapply (sden A) v = inl v.
Proof.
  intros HA Hst Hv; rewrite (named_sdrop_none lenv tenv aenv penv A v Hv).
  unfold settled_tail in Hst; apply andb_true_iff in Hst as [_ Hst].
  destruct (sdrop_none A); [|discriminate]; apply rapply_identity.
Qed.

Lemma bpart_o_spec A B : sdistd A -> bpart_o F A = Some B ->
  sdistd B /\ settled_tail B = negb (has_terms B)
  /\ (forall k, rapply (sden B) (mk_rvar None k) = rapply (sden A) (mk_rvar None k)).
Proof.
  intros HA; unfold bpart_o; destruct (sfind F LNone A) as [e|] eqn:Ef; [|discriminate].
  pose proof (sfind_sound lenv F HF _ _ _ Ef) as He; cbn [Normalise.lden] in He.
  intros H; injection H as <-.
  assert (Hsem : forall k, esem None (Some (ofe e)) k = rapply (sden A) (mk_rvar None k)).
  { intros k; rewrite (rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; exact HA); cbn [v_label v_index].
    rewrite <- He; apply (esem_ofe lenv tenv aenv penv ntm Hntm). }
  assert (Hts : tldist (fst (ofe e))).
  { destruct e as [[ts m]|]; cbn [ofe fst]; [|exact I].
    apply (tldist_iff lenv); intros t Ht; symmetry in He.
    exact (proj2 (proj1 (sdistd_iff lenv A) HA) t (sget_stargets lenv _ _ _ _ He t Ht)). }
  destruct (ofe e) as [ts m] eqn:Eo; cbn [fst] in Hts.
  assert (Hgen : sdistd (SEnt LNone ts m SNil) /\ settled_tail (SEnt LNone ts m SNil) = negb (has_terms (SEnt LNone ts m SNil))
                 /\ forall k, rapply (sden (SEnt LNone ts m SNil)) (mk_rvar None k) = rapply (sden A) (mk_rvar None k)).
  { split; [split; [reflexivity|split; [exact Hts|exact I]]|].
    split; [unfold settled_tail; cbn [sdrop_none]; apply andb_true_r|].
    intros k; rewrite <- Hsem.
    rewrite (rapply_sden lenv tenv aenv penv) by (split; [reflexivity|exact I]); reflexivity. }
  destruct ts as [|t0 r0]; [|exact Hgen]; destruct m as [|m']; [|exact Hgen].
  split; [exact I|split; [reflexivity|]].
  intros k; rewrite <- Hsem; change (sden SNil) with (@ridentity T); rewrite rapply_identity.
  cbn [Normalise.esem tlen Nat.ltb Nat.leb]; do 2 f_equal; lia.
Qed.

Lemma ttail_tset t A A' : ttail t = Some A -> ttail (tset t A') = Some A' /\ forall A'', tset (tset t A') A'' = tset t A''.
Proof.
  destruct t as [g i|u [N|A0 L a w0] [n|]]; cbn [ttail tset]; try discriminate; intros _; split; reflexivity.
Qed.

Lemma ttail_dist t A : ttail t = Some A -> tdist t -> sdistd A.
Proof.
  destruct t as [g i|u [N|A0 L a w0] [n|]]; cbn [ttail]; try discriminate; intros H; injection H as <-; cbn; tauto.
Qed.

Lemma settled_cases t : settled ntm t = true ->
  (is_pure ntm t = true /\ ttail t = None)
  \/ (exists u w b A, t = NBind u w b /\ u < ntm /\ ttail t = Some A /\ settled_tail A = true).
Proof.
  destruct t as [g i|u w b]; cbn [settled]; [discriminate|].
  assert (Hgen : (u <? ntm) && match ttail (NBind u w b) with Some A => settled_tail A | None => false end = true ->
     exists u0 w0 b0 A, NBind u w b = NBind u0 w0 b0 /\ u0 < ntm /\ ttail (NBind u w b) = Some A /\ settled_tail A = true).
  { intros H; apply andb_true_iff in H as [Hu H]; apply Nat.ltb_lt in Hu.
    destruct (ttail (NBind u w b)) as [A|]; [|discriminate]; exists u, w, b, A; auto. }
  destruct w as [[|h ts m r]|A L a w0]; try (intros H; right; exact (Hgen H)).
  destruct b as [n|]; [intros H; right; exact (Hgen H)|].
  intros H; left; split; [exact H|reflexivity].
Qed.

(** What [j] segments do, one after the other. *)
Fixpoint pref (j : nat) (K : lword) : radj T :=
  match j, K with
  | S j', LS s :: K' => rcompose (pref j' K') (sden s)
  | _, _ => ridentity
  end.

Lemma tshift_sound s1 t t' : sdistd s1 -> tdist t -> tshift F ntm s1 t = Some t' ->
  match ttail t with
  | None => t' = t
  | Some A => exists A', t' = tset t A' /\ sdistd A' /\ settled_tail A' = true
                /\ forall k, rapply (sden A') (mk_rvar None k) = cres (sden s1) (rapply (sden A) (mk_rvar None k))
  end.
Proof.
  intros Hs1 Ht; unfold tshift; destruct (ttail t) as [A|] eqn:Et; [|intros H; injection H as <-; reflexivity].
  pose proof (ttail_dist t A Et Ht) as HA.
  destruct (fcomp F ntm s1 A) as [X|] eqn:Ec; [|discriminate]; cbn [obind].
  destruct (fcomp_sound lenv tenv aenv penv F HF ntm Hntm _ _ _ Hs1 HA Ec) as [HX DX].
  destruct (bpart_o F X) as [B|] eqn:Eb; [|discriminate]; cbn [obind].
  destruct (bpart_o_spec X B HX Eb) as [HB [Hst Hk]].
  destruct (has_terms B) eqn:Eh; [discriminate|]; intros H; injection H as <-.
  exists B; split; [reflexivity|split; [exact HB|split; [exact Hst|]]].
  intros k; rewrite Hk, DX, rapply_compose_cres; reflexivity.
Qed.

Lemma tsh_chain_sound j : forall K t t', lwdist K -> tdist t -> tsh_chain F ntm j t K = Some t' ->
  lwden K = rcompose (lwden (skipn j K)) (pref j K)
  /\ match ttail t with
     | None => t' = t
     | Some A => (j = 0 /\ t' = t)
                 \/ exists A', t' = tset t A' /\ sdistd A' /\ settled_tail A' = true
                      /\ forall k, rapply (sden A') (mk_rvar None k) = cres (pref j K) (rapply (sden A) (mk_rvar None k))
     end.
Proof.
  induction j as [|j IH]; intros K t t' HK Ht; cbn [tsh_chain].
  - intros H; injection H as <-; cbn [skipn pref]; split; [rewrite rcompose_identity_r; reflexivity|].
    destruct (ttail t); [left; split; reflexivity|reflexivity].
  - destruct K as [|[s1|L a] K']; try discriminate.
    inversion HK as [|? ? Hs1 HK']; subst.
    destruct (tshift F ntm s1 t) as [t1|] eqn:E1; [|discriminate]; cbn [obind]; intros H.
    pose proof (tshift_sound s1 t t1 Hs1 Ht E1) as H1.
    destruct (ttail t) as [A|] eqn:Et.
    + destruct H1 as [A1 [-> [HA1 [Hst1 Hk1]]]].
      destruct (ttail_tset t A A1 Et) as [Et1 Hset].
      assert (Ht1 : tdist (tset t A1)).
      { destruct t as [g i|u [N|A0 L a w0] [n|]]; cbn [ttail] in Et; try discriminate; cbn; cbn in Ht; tauto. }
      destruct (IH K' (tset t A1) t' HK' Ht1 H) as [D R]; rewrite Et1 in R.
      split; [cbn [skipn pref Layered.lwden]; rewrite D, rcompose_assoc; reflexivity|].
      right; destruct R as [[-> ->]|[A' [-> [HA' [Hst' Hk']]]]].
      * exists A1; split; [reflexivity|split; [exact HA1|split; [exact Hst1|]]].
        intros k; cbn [pref]; rewrite rcompose_identity_l; apply Hk1.
      * exists A'; split; [apply Hset|split; [exact HA'|split; [exact Hst'|]]].
        intros k; rewrite Hk', Hk1; cbn [pref]; rewrite cres_compose; reflexivity.
    + subst t1; destruct (IH K' t t' HK' Ht H) as [D R]; rewrite Et in R.
      split; [cbn [skipn pref Layered.lwden]; rewrite D, rcompose_assoc; reflexivity|exact R].
Qed.

(** A settled term carried [j] segments on has the same meaning, when
    the rest cannot tell what the segments do to named variables. *)
Lemma join_target j K t t' : lwdist K -> tdist t -> settled ntm t = true -> tsh_chain F ntm j t K = Some t' ->
  (forall v, v_label v <> None -> rapply (lwden K) v = rapply (lwden (skipn j K)) v) ->
  tdist t' /\ rapply_target (lwden (skipn j K)) (tden t') = rapply_target (lwden K) (tden t).
Proof.
  intros HK Ht Hset Hc Hn.
  destruct (tsh_chain_sound j K t t' HK Ht Hc) as [D R].
  destruct (settled_cases t Hset) as [[Hp Et]|[u [w [b [A [-> [Hu [Et Hst]]]]]]]].
  - rewrite Et in R; subst t'; split; [exact Ht|].
    symmetry; exact (proj2 (pure_target lenv tenv aenv penv ntm Hntm _ _ t Hp Hn)).
  - rewrite Et in R; destruct R as [[-> ->]|[A' [-> [HA' [Hst' Hk']]]]].
    + split; [exact Ht|]; cbn [skipn]; reflexivity.
    + pose proof (ttail_dist _ A Et Ht) as HA.
      assert (E : rcompose (lwden (skipn j K)) (sden A') = rcompose (lwden K) (sden A)).
      { apply rextensionality; intros [[x|] k]; rewrite !rapply_compose_cres.
        - rewrite (settled_named A' _ HA' Hst') by discriminate; rewrite (settled_named A _ HA Hst) by discriminate.
          cbn [cres]; symmetry; apply Hn; discriminate.
        - rewrite Hk', cres_compose, <- D; reflexivity. }
      destruct (tset_rel lenv tenv aenv penv ntm Hntm (lwden (skipn j K)) (lwden K) 0 0 (le_n 0) _ A A' Et Ht
                  (ex_intro _ u (ex_intro _ w (ex_intro _ b (conj eq_refl Hu)))) HA' E) as [Hd Hr].
      split; [exact Hd|]; apply rtarget_result_inj; rewrite !rapply_target_res; exact Hr.
Qed.

(** *** A segment as a renaming and its terms *)

Local Notation fcomp_ok := (fcomp_sound lenv tenv aenv penv F HF ntm Hntm).
Local Notation sdb := (sdistb_sound lenv F HF).

Lemma unterm_sound s sa Ts : sdistd s -> unterm F ntm s = Some (sa, Ts) ->
  sdistd sa /\ Forall tdist Ts /\ sden s = rcompose (pins (map tden Ts) ridentity) (sden sa).
Proof.
  intros Hs; unfold unterm.
  destruct (fcomp F ntm (shseg LNone (nterms s)) s) as [s1|]; [|discriminate].
  destruct (rents (ents s1) 0) as [es T0']; destruct (rents (ents s) 0) as [es' T0].
  destruct (mkseg F es) as [sa0|]; [|discriminate].
  destruct (tfront F T0 SNil) as [eT|] eqn:Et; [|discriminate].
  destruct (fcomp F ntm eT sa0) as [s2|] eqn:Ec; [|discriminate].
  destruct (seg_eqb s2 s && forallb (tdistb F) T0 && sdistb F sa0) eqn:Eb; [|discriminate].
  intros H; injection H as <- <-.
  apply andb_true_iff in Eb as [Eb H3]; apply andb_true_iff in Eb as [H1 H2].
  apply (proj1 (proj2 (proj2 nf_eqb_eq))) in H1; subst s2.
  pose proof (sdb _ H3) as Hsa.
  assert (HT : Forall tdist T0).
  { apply Forall_forall; intros x Hx; rewrite forallb_forall in H2.
    exact (proj1 (distb_sound lenv F HF) x (H2 x Hx)). }
  destruct (tfront_sound lenv tenv aenv penv F HF ntm Hntm T0 SNil eT I HT Et) as [He De].
  destruct (fcomp_ok _ _ _ He Hsa Ec) as [_ Dc].
  refine (conj Hsa (conj HT _)); rewrite Dc, De; reflexivity.
Qed.

Lemma thread_sound j Ts K Kp : lwdist K -> Forall tdist Ts -> forallb (settled ntm) Ts = true ->
  (forall v, v_label v <> None -> rapply (lwden K) v = rapply (lwden (skipn j K)) v) ->
  thread F ntm j Ts K = Some Kp ->
  lwdist Kp /\ lwden Kp = pins (map (fun t => rapply_target (lwden K) (tden t)) Ts) (lwden K).
Proof.
  intros HK HT Hst Hn; unfold thread.
  destruct (omapl (fun t => tsh_chain F ntm j t K) Ts) as [Ts'|] eqn:Eo; [|discriminate]; cbn [obind]; intros H.
  assert (Hall : Forall tdist Ts'
                 /\ map (fun t => rapply_target (lwden (skipn j K)) (tden t)) Ts'
                    = map (fun t => rapply_target (lwden K) (tden t)) Ts).
  { clear H; revert Ts' Eo; induction Ts as [|t r IH]; intros Ts'; cbn [omapl].
    - intros E; injection E as <-; split; [constructor|cbn [map]; reflexivity].
    - destruct (tsh_chain F ntm j t K) as [t'|] eqn:Et; [|discriminate].
      destruct (omapl (fun t => tsh_chain F ntm j t K) r) as [r'|] eqn:Er; [|discriminate].
      intros E; injection E as <-.
      inversion HT as [|? ? Ht HT']; subst; cbn [forallb] in Hst; apply andb_true_iff in Hst as [Hs1 Hs2].
      destruct (join_target j K t t' HK Ht Hs1 Et Hn) as [Hd' Eq].
      destruct (IH HT' Hs2 r' eq_refl) as [Hr' Em].
      split; [constructor; assumption|]; cbn [map]; rewrite Eq, Em; reflexivity. }
  destruct Hall as [HT' Em].
  destruct (Canon.thread_sound lenv tenv aenv penv F HF ntm Hntm j Ts' K Kp HK HT' H) as [HKp DKp].
  split; [exact HKp|]; rewrite DKp, Em; reflexivity.
Qed.

Lemma lfollow_sound K : lwdist K -> forall g i t d, lfollow F K g i = Some (FT t d) ->
  d <= List.length K
  /\ rapply (lwden K) (mk_rvar (lden g) i) = cres (lwden (skipn (List.length K - d) K)) (rtarget_result (tden t)).
Proof.
  induction K as [|[s|L a] r IH]; intros HK g i t d; cbn [lfollow].
  - intros H; injection H as <- <-; split; [cbn [List.length]; lia|].
    cbn [List.length skipn Layered.lwden Normalise.tden rtarget_result cres]; reflexivity.
  - inversion HK as [|? ? Hs Hr]; subst.
    destruct (seg_tgt F s g i) as [x|] eqn:E; [|discriminate].
    pose proof (proj2 (seg_tgt_sound lenv tenv aenv penv F HF _ _ _ _ Hs E)) as Ex.
    assert (Hterm : Some (FT x (List.length r)) = Some (FT t d) ->
              d <= List.length (LS s :: r)
              /\ rapply (lwden (LS s :: r)) (mk_rvar (lden g) i)
                 = cres (lwden (skipn (List.length (LS s :: r) - d) (LS s :: r))) (rtarget_result (tden t))).
    { intros H; injection H as <- <-; split; [cbn [List.length]; lia|].
      cbn [List.length]; replace (S (List.length r) - List.length r) with 1 by lia; cbn [skipn Layered.lwden].
      rewrite rapply_compose_cres, Ex; reflexivity. }
    destruct x as [g' j'|u w b]; [|exact Hterm].
    intros H; destruct (IH Hr _ _ _ _ H) as [Hd Eq]; split; [cbn [List.length]; lia|].
    cbn [List.length]; replace (S (List.length r) - d) with (S (List.length r - d)) by lia; cbn [skipn Layered.lwden].
    rewrite rapply_compose_cres, Ex; cbn [Normalise.tden rtarget_result cres]; exact Eq.
  - inversion HK as [|? ? _ Hr]; subst.
    destruct (Nat.ltb_spec i (lcn F L g)) as [Hi|Hi]; [|discriminate].
    intros H; destruct (IH Hr _ _ _ _ H) as [Hd Eq]; split; [cbn [List.length]; lia|].
    cbn [List.length]; replace (S (List.length r) - d) with (S (List.length r - d)) by lia; cbn [skipn].
    rewrite (lifted_apply lenv tenv aenv penv F HF ntm Hntm L a r g i Hi); exact Eq.
Qed.

Lemma shared_sound j Ts s1 K0 V : lwdist (LS s1 :: K0) -> Forall tdist Ts -> forallb (settled ntm) Ts = true ->
  (forall v, v_label v <> None -> rapply (lwden (LS s1 :: K0)) v = rapply (lwden (skipn j (LS s1 :: K0))) v) ->
  shared F ntm j Ts s1 K0 = Some V ->
  Forall tdist V
  /\ map (fun t => rapply_target (lwden K0) (tden t)) V
     = map (fun t => rapply_target (lwden (LS s1 :: K0)) (tden t)) Ts.
Proof.
  intros HK HT Hst Hn; unfold shared; set (K := LS s1 :: K0) in *.
  assert (HK0 : lwdist K0) by (inversion HK; assumption).
  revert V; induction Ts as [|t r IH]; intros V; cbn [omapl].
  - intros E; injection E as <-; split; [constructor|cbn [map]; reflexivity].
  - destruct (tsh_chain F ntm j t K) as [t'|] eqn:Et; [|discriminate].
    destruct (trace F K0 (j - 1) t') as [v|]; [|discriminate].
    destruct (lfollow F K0 (fst v) (snd v)) as [[x d|? ? ? ?]|] eqn:El; try discriminate.
    destruct (ntgt_eqb x t' && Nat.eqb (d + j) (S (List.length K0))) eqn:Eb; [|discriminate].
    match goal with |- match ?X with _ => _ end = _ -> _ => destruct X as [r'|] eqn:Er end; [|discriminate].
    intros E; injection E as <-.
    inversion HT as [|? ? Ht HT']; subst; cbn [forallb] in Hst; apply andb_true_iff in Hst as [Hs1 Hs2].
    destruct (IH HT' Hs2 r' eq_refl) as [Hr' Em].
    split; [constructor; [exact I|exact Hr']|]; cbn [map]; rewrite Em; f_equal.
    apply andb_true_iff in Eb as [E1 E2]; apply (proj1 nf_eqb_eq) in E1; subst x; apply Nat.eqb_eq in E2.
    destruct (join_target j K t t' HK Ht Hs1 Et Hn) as [_ Eq].
    destruct (lfollow_sound K0 HK0 _ _ _ _ El) as [Hd Ef].
    apply rtarget_result_inj; rewrite <- Eq, !rapply_target_res; cbn [Normalise.tden rtarget_result cres].
    rewrite Ef; replace (List.length K0 - d) with (j - 1) by lia.
    destruct j as [|j'']; [lia|]; unfold K; cbn [skipn]; replace (S j'' - 1) with j'' by lia; reflexivity.
Qed.

Lemma try_join_sound s s1 K0 r : sdistd s -> lwdist (LS s1 :: K0) ->
  try_join F ntm s s1 K0 = Some r ->
  match r with
  | JShare c => sdistd c /\ rcompose (lwden K0) (sden c) = rcompose (lwden (LS s1 :: K0)) (sden s)
  | JThread j sa Kp =>
      sdistd sa /\ lwdist Kp /\ rcompose (lwden Kp) (sden sa) = rcompose (lwden (LS s1 :: K0)) (sden s)
  | JPart se em => sdistd se /\ sdistd em /\ rcompose (sden em) (sden se) = sden s
  end.
Proof.
  intros Hs HK; unfold try_join; cbn zeta; set (K := LS s1 :: K0) in *.
  assert (Hs1 : sdistd s1) by (inversion HK; assumption).
  destruct (named_term s1); [discriminate|].
  destruct (scan F ntm true SNil K 0) as [j'|] eqn:Esc; [|discriminate].
  destruct (match skipn (j' - 1) K with LS sj :: Kj1 => _ | _ => false end); [|discriminate].
  destruct (unterm F ntm s) as [[sa' Ts]|] eqn:Eu; [|discriminate]; cbn [obind].
  destruct (unterm_sound s sa' Ts Hs Eu) as [Hsa [HT Ds]].
  destruct (forallb (settled ntm) Ts) eqn:Est; [|discriminate].
  assert (Hn : forall v, v_label v <> None -> rapply (lwden K) v = rapply (lwden (skipn j' K)) v).
  { intros v Hv; pose proof (scan_sound K true SNil 0 j' v I (fun _ => conj I lpres_nil) HK Esc Hv) as E.
    change (sden SNil) with (@ridentity T) in E; rewrite rapply_identity, Nat.sub_0_r in E; exact E. }
  destruct (obind (shared F ntm j' Ts s1 K0) _) as [c|] eqn:Esh.
  { intros H; injection H as <-.
    destruct (shared F ntm j' Ts s1 K0) as [V|] eqn:EV; [|discriminate]; cbn [obind] in Esh.
    destruct (tfront F V s1) as [X|] eqn:EX; [|discriminate]; cbn [obind] in Esh.
    destruct (shared_sound j' Ts s1 K0 V HK HT Est Hn EV) as [HV Em].
    destruct (tfront_sound lenv tenv aenv penv F HF ntm Hntm V s1 X Hs1 HV EX) as [HX DX].
    destruct (fcomp_ok _ _ _ HX Hsa Esh) as [Hc Dc]; split; [exact Hc|].
    rewrite Dc, rcompose_assoc, DX, pins_compose_l, map_map, Em.
    rewrite Ds, (rcompose_assoc (lwden K)), pins_compose_l, rcompose_identity_r, map_map; reflexivity. }
  destruct (forallb (fun b : bool => b) _).
  - destruct (thread F ntm j' Ts K) as [Kp'|] eqn:Et; [|discriminate]; cbn [obind]; intros H; injection H as <-.
    destruct (thread_sound j' Ts K Kp' HK HT Est Hn Et) as [HKp DKp].
    split; [exact Hsa|split; [exact HKp|]].
    rewrite DKp, Ds, (rcompose_assoc (lwden K)), pins_compose_l, rcompose_identity_r, map_map; reflexivity.
  - destruct (map snd _) as [|m0 M0]; [discriminate|].
    destruct (sset F LNone _ _ SNil) as [e|]; [|discriminate].
    destruct (tfront F (m0 :: M0) SNil) as [em|]; [|discriminate].
    destruct (tfront F Ts SNil) as [eT|] eqn:EeT; [|discriminate].
    destruct (fcomp F ntm em e) as [c|] eqn:Ec; [|discriminate].
    destruct (fcomp F ntm e sa') as [se|] eqn:Ese; [|discriminate].
    destruct (seg_eqb c eT && sdistb F e && sdistb F em && sdistb F se) eqn:Eb; [|discriminate].
    intros H; injection H as <-.
    apply andb_true_iff in Eb as [Eb H4]; apply andb_true_iff in Eb as [Eb H3]; apply andb_true_iff in Eb as [H1 H2].
    apply (proj1 (proj2 (proj2 nf_eqb_eq))) in H1; subst c.
    pose proof (sdb _ H2) as He; pose proof (sdb _ H3) as Hem; pose proof (sdb _ H4) as Hse.
    destruct (fcomp_ok _ _ _ Hem He Ec) as [_ Dc]; destruct (fcomp_ok _ _ _ He Hsa Ese) as [_ Dse].
    destruct (tfront_sound lenv tenv aenv penv F HF ntm Hntm Ts SNil eT I HT EeT) as [_ DeT].
    split; [exact Hse|split; [exact Hem|]].
    rewrite Dse, rcompose_assoc, <- Dc, DeT, Ds; reflexivity.
Qed.


Lemma swap_sound s s1 sa f1 n rho : sdistd s -> sdistd s1 -> swap F ntm s s1 = Some (sa, f1, n, rho) ->
  sdistd sa /\ sdistd f1 /\ sdistd n /\ sdistd rho
  /\ rcompose (sden rho) (rcompose (sden n) (rcompose (sden f1) (sden sa))) = rcompose (sden s1) (sden s).
Proof.
  intros Hs Hs1; unfold swap.
  destruct (sinv F (sdrop_none s1)) as [[nu R]|]; [|discriminate].
  destruct (unterm F ntm s) as [[sa' Ts]|] eqn:Eu; [|discriminate].
  destruct (slifts F ntm (List.length Ts) s1) as [f1'|]; [|discriminate].
  destruct (obind (omapl (tshift F ntm s1) Ts) _) as [n'|]; [|discriminate].
  destruct (sset F LNone (tl_of R) 0 (sdrop_none s1)) as [rho'|]; [|discriminate].
  destruct (fcomp F ntm s1 s) as [c1|] eqn:E1; [|discriminate].
  destruct (fcomp F ntm f1' sa') as [t1|] eqn:Et1; [|discriminate]; cbn [obind].
  destruct (fcomp F ntm n' t1) as [t2|] eqn:Et2; [|discriminate]; cbn [obind].
  destruct (fcomp F ntm rho' t2) as [c2|] eqn:Et3; [|discriminate].
  destruct (seg_eqb c1 c2 && forallb (settled ntm) Ts && sdistb F f1' && sdistb F n' && sdistb F rho') eqn:Eb; [|discriminate].
  intros H; injection H as <- <- <- <-.
  apply andb_true_iff in Eb as [Eb H5]; apply andb_true_iff in Eb as [Eb H4]; apply andb_true_iff in Eb as [Eb H3].
  apply andb_true_iff in Eb as [H1 _].
  apply (proj1 (proj2 (proj2 nf_eqb_eq))) in H1; subst c2.
  pose proof (sdb _ H3) as Hf; pose proof (sdb _ H4) as Hn; pose proof (sdb _ H5) as Hr.
  destruct (unterm_sound s sa' Ts Hs Eu) as [Hsa _].
  destruct (fcomp_ok _ _ _ Hs1 Hs E1) as [_ D1].
  destruct (fcomp_ok _ _ _ Hf Hsa Et1) as [Ht1 Dt1].
  destruct (fcomp_ok _ _ _ Hn Ht1 Et2) as [Ht2 Dt2].
  destruct (fcomp_ok _ _ _ Hr Ht2 Et3) as [_ Dt3].
  refine (conj Hsa (conj Hf (conj Hn (conj Hr _)))); rewrite <- D1, Dt3, Dt2, Dt1; reflexivity.
Qed.

(** *** One segment for each term *)

Lemma split1_sound t E' N' rho E0 : split1 F ntm t = Some (Some (E', N', rho)) -> tfront F [t] SNil = Some E0 ->
  sdistd E' /\ sdistd N' /\ sdistd rho /\ rcompose (sden rho) (rcompose (sden N') (sden E')) = sden E0.
Proof.
  unfold split1; destruct (tsplit t) as [[N mk]|]; [|discriminate].
  destruct (sinv_b F N) as [[nu R]|]; [|discriminate].
  destruct (obind (mk (List.length R)) _) as [E1|]; [|discriminate].
  destruct (slifts F ntm (List.length R) N) as [N1|]; [|discriminate].
  destruct (sset F LNone (tl_of R) 0 SNil) as [rho1|]; [|discriminate].
  destruct (tfront F [t] SNil) as [E00|]; [|discriminate].
  destruct (fcomp F ntm N1 E1) as [x|] eqn:Ex; [|discriminate]; cbn [obind].
  destruct (fcomp F ntm rho1 x) as [c|] eqn:Ec; [|discriminate].
  destruct (seg_eqb c E00 && sdistb F E1 && sdistb F N1 && sdistb F rho1) eqn:Eb; [|discriminate].
  intros H H0; injection H as <- <- <-; injection H0 as <-.
  apply andb_true_iff in Eb as [Eb H4]; apply andb_true_iff in Eb as [Eb H3]; apply andb_true_iff in Eb as [H1 H2].
  apply (proj1 (proj2 (proj2 nf_eqb_eq))) in H1; subst c.
  pose proof (sdb _ H2) as HE; pose proof (sdb _ H3) as HN; pose proof (sdb _ H4) as Hr.
  destruct (fcomp_ok _ _ _ HN HE Ex) as [Hx Dx]; destruct (fcomp_ok _ _ _ Hr Hx Ec) as [_ Dc].
  refine (conj HE (conj HN (conj Hr _))); rewrite Dc, Dx; reflexivity.
Qed.

(** The segments of a list, one after the other, after [X]. *)
Fixpoint chain (tes : list (ntgt * seg)) (X : radj T) : radj T :=
  match tes with [] => X | te :: r => chain r (rcompose (sden (snd te)) X) end.

Lemma fold_fcomp_none (tes : list (ntgt * seg)) :
  fold_left (fun acc te => obind acc (fun g => fcomp F ntm (snd te) g)) tes None = None.
Proof. induction tes as [|te r IH]; [reflexivity|exact IH]. Qed.

Lemma fold_fcomp_sound tes : forall x c, Forall (fun te => sdistd (snd te)) tes -> sdistd x ->
  fold_left (fun acc te => obind acc (fun g => fcomp F ntm (snd te) g)) tes (Some x) = Some c ->
  sden c = chain tes (sden x).
Proof.
  induction tes as [|te r IH]; intros x c HT Hx; cbn [fold_left chain].
  - intros H; injection H as <-; reflexivity.
  - inversion HT as [|? ? Hte HT']; subst; cbn [obind].
    destruct (fcomp F ntm (snd te) x) as [y|] eqn:Ey; [|rewrite fold_fcomp_none; discriminate].
    destruct (fcomp_ok _ _ _ Hte Hx Ey) as [Hy Dy]; intros H; rewrite (IH y c HT' Hy H), Dy; reflexivity.
Qed.

Lemma singles_sound s sa tes : sdistd s -> singles F ntm s = Some (sa, tes) ->
  sdistd sa /\ Forall (fun te => sdistd (snd te) /\ tfront F [fst te] SNil = Some (snd te)) tes
  /\ sden s = chain tes (sden sa).
Proof.
  intros Hs; unfold singles.
  destruct (unterm F ntm s) as [[sa0 Ts]|] eqn:Eu; [|discriminate].
  destruct (unterm_sound s sa0 Ts Hs Eu) as [Hsa _].
  destruct (omapl _ _) as [tes0|] eqn:Eo; [|discriminate].
  destruct (fold_left _ tes0 (Some sa0)) as [c|] eqn:Ef; [|discriminate].
  destruct (seg_eqb c s && forallb (fun te => sdistb F (snd te)) tes0) eqn:Eb; [|discriminate].
  intros H; injection H as <- <-.
  apply andb_true_iff in Eb as [H1 H2]; apply (proj1 (proj2 (proj2 nf_eqb_eq))) in H1; subst c.
  assert (HT : Forall (fun te => sdistd (snd te) /\ tfront F [fst te] SNil = Some (snd te)) tes0).
  { apply Forall_forall; intros te Hte; rewrite forallb_forall in H2; split; [exact (sdb _ (H2 te Hte))|].
    destruct (omapl_in _ _ _ _ Eo Hte) as [x [_ Hx]].
    destruct (tfront F [x] SNil) as [e|] eqn:Ee; [|discriminate]; cbn [option_map] in Hx; injection Hx as <-; exact Ee. }
  refine (conj Hsa (conj HT _)).
  apply (fold_fcomp_sound tes0 sa0 s); [|exact Hsa|exact Ef].
  apply Forall_forall; intros te Hte; exact (proj1 (proj1 (Forall_forall _ _) HT te Hte)).
Qed.

(** *** The pieces of the cons *)

Definition cc_ok (cc : seg -> lword -> option lword) : Prop :=
  forall s K K', sdistd s -> lwdist K -> cc s K = Some K' -> lwdist K' /\ lwden K' = rcompose (lwden K) (sden s).

Lemma cc0_ok cc (Hcc : cc_ok cc) : cc_ok (fun x K0 => match x with SNil => Some K0 | _ => cc x K0 end).
Proof.
  intros s K K' Hs HK; destruct s as [|h ts m r]; [|exact (Hcc _ K K' Hs HK)].
  intros H; injection H as <-; split; [exact HK|].
  change (sden SNil) with (@ridentity T); rewrite rcompose_identity_r; reflexivity.
Qed.

Lemma reroute_c_sound s K : sdistd s -> lwdist K ->
  sdistd (reroute_c F ntm s K) /\ rcompose (lwden K) (sden (reroute_c F ntm s K)) = rcompose (lwden K) (sden s).
Proof.
  intros Hs HK; unfold reroute_c; destruct (reroute_g F ntm s K) as [x|] eqn:E; [|split; [exact Hs|reflexivity]].
  exact (reroute_g_sound lenv tenv aenv penv F HF ntm Hntm s K x Hs HK E).
Qed.

Lemma rr_up_sound n : forall l, lwdist l -> lwdist (rr_up F ntm n l) /\ lwden (rr_up F ntm n l) = lwden l.
Proof.
  induction n as [|n IH]; intros l Hl; [split; [exact Hl|reflexivity]|].
  destruct l as [|[x|L a] r]; cbn [rr_up]; try (split; [exact Hl|reflexivity]).
  inversion Hl as [|? ? Hx Hr]; subst; destruct (IH r Hr) as [Hr' Dr'].
  change (lwden (LS x :: r)) with (rcompose (lwden r) (sden x)); rewrite <- Dr'.
  destruct (rr_up F ntm n r) as [|[y|L a] r'] eqn:E.
  - split; [constructor; assumption|reflexivity].
  - destruct (reroute_c_sound x (LS y :: r') Hx Hr') as [Hx' Dx'].
    split; [constructor; assumption|].
    change (lwden (LS (reroute_c F ntm x (LS y :: r')) :: LS y :: r'))
      with (rcompose (lwden (LS y :: r')) (sden (reroute_c F ntm x (LS y :: r')))).
    exact Dx'.
  - split; [constructor; assumption|reflexivity].
Qed.

Lemma recons_sound cc (Hcc : cc_ok cc) p : forall K K', lwdist K -> recons cc p K = Some K' ->
  lwdist K' /\ lwden K' = lwden K.
Proof.
  induction p as [|p IH]; intros K K' HK; cbn [recons]; [intros H; injection H as <-; split; [exact HK|reflexivity]|].
  destruct K as [|[x|L a] r]; try (intros H; injection H as <-; split; [exact HK|reflexivity]).
  inversion HK as [|? ? Hx Hr]; subst.
  destruct (recons cc p r) as [r'|] eqn:E; [|discriminate]; cbn [obind]; intros H.
  destruct (IH r r' Hr E) as [Hr' Dr'].
  destruct (cc0_ok cc Hcc x r' K' Hx Hr' H) as [A B]; split; [exact A|].
  rewrite B, Dr'; reflexivity.
Qed.

Lemma sweep_sound cc (Hcc : cc_ok cc) n : forall s K K', sdistd s -> lwdist K -> sweep F ntm cc n s K = Some K' ->
  lwdist K' /\ lwden K' = rcompose (lwden K) (sden s).
Proof.
  induction n as [|n IH]; intros s K K' Hs HK; [exact (Hcc s K K' Hs HK)|].
  destruct K as [|[s1|L a] K0]; cbn [sweep]; try exact (Hcc s _ K' Hs HK).
  inversion HK as [|? ? Hs1 HK0]; subst.
  destruct (iface F ntm s (LS s1 :: K0)) as [s' io] eqn:Ei.
  destruct (iface_sound s _ s' io Hs HK Ei) as [Hs' [Hio D]].
  assert (H1 : forall s1', match io with SNil => Some s1 | _ => fcomp F ntm s1 io end = Some s1' ->
            sdistd s1' /\ sden s1' = rcompose (sden s1) (sden io)).
  { intros s1'; destruct io as [|h ts m r]; [|exact (fcomp_ok _ _ _ Hs1 Hio)].
    intros H; injection H as <-; split; [exact Hs1|].
    change (sden SNil) with (@ridentity T); rewrite rcompose_identity_r; reflexivity. }
  destruct (match io with SNil => Some s1 | _ => fcomp F ntm s1 io end) as [s1'|]; [|discriminate].
  destruct (H1 s1' eq_refl) as [Hs1' D1].
  assert (Hgen : forall X, lwdist X -> lwden X = rcompose (lwden K0) (sden s1') ->
            forall Y, lwdist Y /\ lwden Y = rcompose (lwden X) (sden s') ->
            lwdist Y /\ lwden Y = rcompose (lwden (LS s1 :: K0)) (sden s)).
  { intros X HX DX Y [A B]; split; [exact A|]; rewrite B, DX, D1, <- D; cbn [Layered.lwden].
    rewrite !rcompose_assoc; reflexivity. }
  destruct s1' as [|h ts m r].
  { intros H; refine (Hgen K0 HK0 _ K' (Hcc s' K0 K' Hs' HK0 H)).
    change (sden SNil) with (@ridentity T); rewrite rcompose_identity_r; reflexivity. }
  set (s1' := SEnt h ts m r) in *.
  destruct (has_terms s1' && has_terms s').
  - destruct (sweep F ntm cc n s1' K0) as [K1|] eqn:E1; [|discriminate]; cbn [option_map]; intros H; injection H as <-.
    destruct (IH s1' K0 K1 Hs1' HK0 E1) as [H1' D1'].
    apply (Hgen K1 H1' D1'); split; [constructor; assumption|reflexivity].
  - destruct (has_terms s1').
    + destruct (sweep F ntm cc n s1' K0) as [K1|] eqn:E1; [|discriminate]; cbn [obind]; intros H.
      destruct (IH s1' K0 K1 Hs1' HK0 E1) as [H1' D1'].
      exact (Hgen K1 H1' D1' K' (Hcc s' K1 K' Hs' H1' H)).
    + destruct (cc s1' K0) as [K1|] eqn:E1; [|discriminate]; cbn [obind]; intros H.
      destruct (Hcc s1' K0 K1 Hs1' HK0 E1) as [H1' D1'].
      exact (Hgen K1 H1' D1' K' (Hcc s' K1 K' Hs' H1' H)).
Qed.

(** *** Segments the rest cannot tell apart *)

Lemma seg_tgt_default s g ts m j : entry_of F s g = Some (ts, m) -> List.length ts <= j ->
  exists x, seg_tgt F s g j = Some x /\ tden x = RRename (mk_rvar (lden g) (j - List.length ts + m)).
Proof.
  unfold entry_of, seg_tgt; destruct (sfind F g s) as [[[ts0 m0]|]|]; cbn [ofe]; try discriminate.
  - intros H; injection H as <- <-; rewrite <- tlen_list; intros Hj.
    rewrite (proj2 (Nat.ltb_ge _ _) Hj); eexists; split; reflexivity.
  - intros H; injection H as <- <-; intros _; eexists; split; [reflexivity|].
    cbn [Normalise.tden List.length]; do 2 f_equal; lia.
Qed.

Lemma seg_keqx_sound tk K s s' :
  (forall x y, tdist x -> tdist y -> tk x y = true ->
     cres (lwden K) (rtarget_result (tden y)) = cres (lwden K) (rtarget_result (tden x))) ->
  sdistd s -> sdistd s' -> lwdist K -> seg_keqx F tk K s s' = true ->
  rcompose (lwden K) (sden s') = rcompose (lwden K) (sden s).
Proof.
  intros Htk Hs Hs' HK H; unfold seg_keqx in H; rewrite forallb_forall in H.
  set (labs := nodup_l (LNone :: seg_labels s ++ seg_labels s') []) in H.
  assert (HA : forall g, In g labs -> forall j,
            cres (lwden K) (rapply (sden s') (mk_rvar (lden g) j)) = cres (lwden K) (rapply (sden s) (mk_rvar (lden g) j))).
  { intros g Hg j; specialize (H g Hg).
    destruct (entry_of F s g) as [[ts m]|] eqn:E1; [|discriminate].
    destruct (entry_of F s' g) as [[ts' m']|] eqn:E2; [|discriminate].
    apply andb_true_iff in H as [Hm Hj]; apply Nat.eqb_eq in Hm; rewrite forallb_forall in Hj.
    destruct (Nat.ltb_spec j (Nat.max (List.length ts) (List.length ts'))) as [Hlt|Hge].
    - specialize (Hj j (proj2 (in_seq _ _ _) (conj (Nat.le_0_l _) Hlt))).
      destruct (seg_tgt F s g j) as [x|] eqn:Ex; [|discriminate].
      destruct (seg_tgt F s' g j) as [y|] eqn:Ey; [|discriminate].
      destruct (seg_tgt_sound lenv tenv aenv penv F HF _ _ _ _ Hs Ex) as [Dx Rx].
      destruct (seg_tgt_sound lenv tenv aenv penv F HF _ _ _ _ Hs' Ey) as [Dy Ry]; rewrite Rx, Ry.
      apply orb_true_iff in Hj as [Hj|Hj]; [apply (proj1 nf_eqb_eq) in Hj; subst y; reflexivity|].
      destruct x as [g1 i1|u1 w1 b1]; destruct y as [g2 i2|u2 w2 b2]; try discriminate; [|exact (Htk _ _ Dx Dy Hj)].
      apply okey_eqb_eq in Hj as [k [K1 K2]]; cbn [Normalise.tden rtarget_result cres].
      symmetry; exact (vfollow_sound lenv tenv aenv penv F HF ntm Hntm K HK _ _ _ _ k K1 K2).
    - pose proof (Nat.le_max_l (List.length ts) (List.length ts')) as Hl1.
      pose proof (Nat.le_max_r (List.length ts) (List.length ts')) as Hl2.
      destruct (seg_tgt_default s g ts m j E1 (Nat.le_trans _ _ _ Hl1 Hge)) as [x [Ex Dx]].
      destruct (seg_tgt_default s' g ts' m' j E2 (Nat.le_trans _ _ _ Hl2 Hge)) as [y [Ey Dy]].
      rewrite (proj2 (seg_tgt_sound lenv tenv aenv penv F HF _ _ _ _ Hs Ex)),
              (proj2 (seg_tgt_sound lenv tenv aenv penv F HF _ _ _ _ Hs' Ey)), Dx, Dy.
      pose proof (Nat.le_trans _ _ _ Hl1 Hge); pose proof (Nat.le_trans _ _ _ Hl2 Hge).
      cbn [rtarget_result cres].
      replace (j - List.length ts' + m') with (j - List.length ts + m) by lia; reflexivity. }
  apply rextensionality; intros [l j]; rewrite !rapply_compose_cres.
  assert (Hin : forall x ts m, (sget l x = Some (ts, m)) -> (x = s \/ x = s') -> exists g, In g labs /\ lden g = l).
  { intros x ts m Eg Hx; destruct (sget_label lenv l x ts m Eg) as [h [Hh [Hl _]]]; exists h; split; [|exact Hl].
    apply nodup_l_in0; right; apply in_or_app; destruct Hx as [->| ->]; [left|right]; exact Hh. }
  destruct (sget l s) as [[ts m]|] eqn:E1.
  { destruct (Hin s ts m E1 (or_introl eq_refl)) as [g [Hg <-]]; exact (HA g Hg j). }
  destruct (sget l s') as [[ts m]|] eqn:E2.
  { destruct (Hin s' ts m E2 (or_intror eq_refl)) as [g [Hg <-]]; exact (HA g Hg j). }
  rewrite !(rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; assumption); cbn [v_label v_index].
  rewrite E1, E2; reflexivity.
Qed.

Lemma seg_keq0_sound K s s' : sdistd s -> sdistd s' -> lwdist K -> seg_keq0 F K s s' = true ->
  rcompose (lwden K) (sden s') = rcompose (lwden K) (sden s).
Proof. apply seg_keqx_sound; intros x y _ _ H; discriminate H. Qed.

Lemma seg_keq_sound K s s' : sdistd s -> sdistd s' -> lwdist K -> seg_keq F ntm K s s' = true ->
  rcompose (lwden K) (sden s') = rcompose (lwden K) (sden s).
Proof.
  intros Hs Hs' HK; apply seg_keqx_sound; [|exact Hs|exact Hs'|exact HK].
  intros x y Dx Dy; unfold tkeq; destruct x as [g i|u w b]; [discriminate|].
  destruct (ttail (NBind u w b)) as [A|] eqn:Ea; [|discriminate].
  destruct (ttail y) as [A'|] eqn:Ea'; [|discriminate]; intros H.
  apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
  apply Nat.ltb_lt in H1; apply (proj1 nf_eqb_eq) in H2; subst y.
  pose proof (ttail_dist _ _ Ea Dx) as HA; pose proof (ttail_dist _ _ Ea' Dy) as HA'.
  exact (proj2 (tset_rel lenv tenv aenv penv ntm Hntm (lwden K) (lwden K) 0 0 (le_n 0) _ A A' Ea Dx
                  (ex_intro _ u (ex_intro _ w (ex_intro _ b (conj eq_refl H1)))) HA'
                  (seg_keq0_sound K A A' HA HA' HK H3))).
Qed.

(** *** Segments composed into one *)

Lemma lwden_app l : forall r, lwden (l ++ r) = rcompose (lwden r) (lwden l).
Proof.
  induction l as [|[s|L a] l IH]; intros r; cbn [app Layered.lwden].
  - rewrite rcompose_identity_r; reflexivity.
  - rewrite IH, rcompose_assoc; reflexivity.
  - rewrite IH, rcompose_assoc; reflexivity.
Qed.

Lemma lwdist_app l r : lwdist l -> lwdist r -> lwdist (l ++ r).
Proof. intros Hl Hr; apply Forall_app; split; assumption. Qed.

Lemma fold_comp_none (l : list seg) : fold_left (fun acc s => obind acc (fun g => fcomp F ntm s g)) l None = None.
Proof. induction l as [|x r IH]; [reflexivity|exact IH]. Qed.

Lemma comp_fold l : forall x Sg, sdistd x -> Forall sdistd l ->
  fold_left (fun acc s => obind acc (fun g => fcomp F ntm s g)) l (Some x) = Some Sg ->
  sdistd Sg /\ sden Sg = rcompose (lwden (map LS l)) (sden x).
Proof.
  induction l as [|y r IH]; intros x Sg Hx Hl; cbn [fold_left map Layered.lwden].
  - intros H; injection H as <-; split; [exact Hx|rewrite rcompose_identity_l; reflexivity].
  - inversion Hl as [|? ? Hy Hr]; subst; cbn [obind].
    destruct (fcomp F ntm y x) as [z|] eqn:Ez; [|rewrite fold_comp_none; discriminate].
    destruct (fcomp_ok _ _ _ Hy Hx Ez) as [Hz Dz]; intros H.
    destruct (IH z Sg Hz Hr H) as [A B]; split; [exact A|]; rewrite B, Dz, rcompose_assoc; reflexivity.
Qed.

Lemma comp_sound l Sg : Forall sdistd l -> comp F ntm l = Some Sg -> sdistd Sg /\ sden Sg = lwden (map LS l).
Proof.
  destruct l as [|x r]; cbn [comp]; [discriminate|]; intros Hl H.
  inversion Hl as [|? ? Hx Hr]; subst.
  destruct (comp_fold r x Sg Hx Hr H) as [A B]; split; [exact A|exact B].
Qed.

Lemma segs_len_le l : List.length (segs_of l) <= List.length l.
Proof.
  induction l as [|[s|L a] r IH]; [apply le_n| |].
  - change (segs_of (LS s :: r)) with (s :: segs_of r); cbn [List.length]; lia.
  - change (segs_of (LA L a :: r)) with (segs_of r); cbn [List.length]; lia.
Qed.

Lemma segs_all l : List.length (segs_of l) = List.length l -> l = map LS (segs_of l).
Proof.
  induction l as [|[s|L a] r IH]; [reflexivity| |].
  - change (segs_of (LS s :: r)) with (s :: segs_of r); cbn [List.length map]; intros H; f_equal; apply IH; lia.
  - change (segs_of (LA L a :: r)) with (segs_of r); cbn [List.length]; intros H.
    pose proof (segs_len_le r); lia.
Qed.

Lemma segs_dist l : lwdist l -> Forall sdistd (segs_of l).
Proof.
  induction 1 as [|[s|L a] r Hx _ IH]; [constructor| |exact IH].
  change (segs_of (LS s :: r)) with (s :: segs_of r); constructor; assumption.
Qed.

Lemma map_LS_dist l : Forall sdistd l -> lwdist (map LS l).
Proof. induction 1; cbn; constructor; assumption. Qed.

(** *** The hop *)

Lemma firstn_segs p K : List.length (segs_of (firstn p K)) = p -> K = map LS (segs_of (firstn p K)) ++ skipn p K.
Proof.
  intros H; rewrite <- (firstn_skipn p K) at 1; f_equal; apply segs_all.
  pose proof (segs_len_le (firstn p K)); pose proof (firstn_le_length p K); lia.
Qed.

Lemma map_LS_inv l : lwdist (map LS l) -> Forall sdistd l.
Proof. induction l as [|x r IH]; cbn [map]; intros H; [constructor|]; inversion H; subst; constructor; [assumption|apply IH; assumption]. Qed.

Lemma hop_chk_sound L a p K Sp1 e0 L2 Kx : lwdist K -> hop_chk F ntm L a p K Sp1 e0 L2 Kx = true ->
  sdistd e0 /\ lwdist Kx /\ rcompose (lwden (LA L2 a :: Kx)) (sden e0) = lwden (LA L a :: K).
Proof.
  intros HK; unfold hop_chk.
  remember (segs_of (firstn p K)) as segs eqn:Esegs; remember (skipn p K) as K2 eqn:EK2.
  intros H; apply andb_true_iff in H as [Hp H]; apply Nat.eqb_eq in Hp.
  assert (EK : K = map LS segs ++ K2) by (subst segs K2; apply firstn_segs; exact Hp).
  assert (HKs : Forall sdistd segs /\ lwdist K2).
  { rewrite EK in HK; apply Forall_app in HK as [H1 H2]; split; [exact (map_LS_inv _ H1)|exact H2]. }
  destruct HKs as [Hsegs HK2].
  destruct (rev segs) as [|Sp rpre] eqn:Er; [discriminate|].
  assert (Es : segs = rev rpre ++ [Sp]) by (rewrite <- (rev_involutive segs), Er; reflexivity).
  apply andb_true_iff in H as [Hk H].
  assert (Hpre : Forall sdistd (rev rpre) /\ sdistd Sp).
  { rewrite Es in Hsegs; apply Forall_app in Hsegs as [H1 H2]; split; [exact H1|inversion H2; assumption]. }
  destruct Hpre as [Hpre HSp].
  assert (H1 : sdistd Sp1 /\ rcompose (lwden K2) (sden Sp1) = rcompose (lwden K2) (sden Sp)).
  { apply orb_true_iff in Hk as [Hk|Hk].
    - apply (proj1 (proj2 (proj2 nf_eqb_eq))) in Hk; subst Sp1; split; [exact HSp|reflexivity].
    - apply andb_true_iff in Hk as [Hk Hd]; pose proof (sdb _ Hd) as HSp1; split; [exact HSp1|].
      exact (seg_keq_sound K2 Sp Sp1 HSp HSp1 HK2 Hk). }
  destruct H1 as [HSp1 E1].
  cbn zeta in H.
  destruct (comp F ntm (rev (Sp1 :: rpre))) as [Sg|] eqn:Ec; [|discriminate].
  destruct (comp F ntm (segs_of (firstn p Kx))) as [Sg'|] eqn:Ec'; [|discriminate].
  destruct (wcomp F ntm (WAtom Sg L a (WEnd SNil)) (WEnd SNil)) as [w1|] eqn:Ew1; [|discriminate].
  destruct (wcomp F ntm (WAtom Sg' L2 a (WEnd SNil)) (WEnd e0)) as [w2|] eqn:Ew2; [|discriminate].
  apply andb_true_iff in H as [H H4]; apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [Hw H2].
  apply (proj2 (proj2 (proj2 nf_eqb_eq))) in Hw; subst w2.
  apply lword_eqb_eq in H4; pose proof (sdb _ H2) as He0.
  assert (Hsx : Forall sdistd (segs_of (firstn p Kx))).
  { apply Forall_forall; intros x Hx; rewrite forallb_forall in H3; exact (sdb _ (H3 x Hx)). }
  assert (Hs1 : Forall sdistd (rev (Sp1 :: rpre))).
  { cbn [rev]; apply Forall_app; split; [exact Hpre|constructor; [exact HSp1|constructor]]. }
  destruct (comp_sound _ Sg Hs1 Ec) as [HSg DSg]; destruct (comp_sound _ Sg' Hsx Ec') as [HSg' DSg'].
  assert (Hw1 : wdist (WAtom Sg L a (WEnd SNil))) by (split; [exact HSg|exact I]).
  assert (Hw2 : wdist (WAtom Sg' L2 a (WEnd SNil))) by (split; [exact HSg'|exact I]).
  assert (Hw0 : wdist (WEnd SNil)) by exact I.
  assert (Hwe : wdist (WEnd e0)) by exact He0.
  pose proof (proj2 (wcomp_sound lenv tenv aenv penv F HF ntm Hntm _ _ _ Hw1 Hw0 Ew1)) as D1.
  pose proof (proj2 (wcomp_sound lenv tenv aenv penv F HF ntm Hntm _ _ _ Hw2 Hwe Ew2)) as D2.
  rewrite D1 in D2; rewrite !wden_atom, !(wden_id lenv tenv aenv penv), wden_end, !rcompose_identity_r in D2.
  split; [exact He0|]; split; [rewrite H4; apply lwdist_app; [apply map_LS_dist; exact Hsx|exact HK2]|].
  assert (EP : lwden (map LS segs) = rcompose (sden Sp) (lwden (map LS (rev rpre)))).
  { rewrite Es, map_app, lwden_app; cbn [map Layered.lwden]; rewrite rcompose_identity_l; reflexivity. }
  assert (EG : sden Sg = rcompose (sden Sp1) (lwden (map LS (rev rpre)))).
  { rewrite DSg; cbn [rev]; rewrite map_app, lwden_app; cbn [map Layered.lwden]; rewrite rcompose_identity_l; reflexivity. }
  assert (EKx : lwden Kx = rcompose (lwden K2) (sden Sg')) by (rewrite H4, lwden_app, DSg'; reflexivity).
  assert (EKK : lwden K = rcompose (lwden K2) (sden Sg)).
  { rewrite EK at 1; rewrite lwden_app, EP, EG, !rcompose_assoc, E1; reflexivity. }
  cbn [Layered.lwden]; rewrite EKx, EKK, <- !rcompose_assoc.
  rewrite <- !rcompose_assoc in D2; rewrite D2; reflexivity.
Qed.

Lemma first_some_in {A B} (f : A -> option B) l y : first_some f l = Some y -> exists x, f x = Some y.
Proof.
  induction l as [|x r IH]; cbn [first_some]; [discriminate|].
  destruct (f x) as [z|] eqn:E; [intros H; injection H as <-; exists x; exact E|exact IH].
Qed.

Lemma hop_at_sound L a p K e0 L2 Kx : lwdist K -> hop_at F ntm L a p K = Some (e0, L2, Kx) ->
  sdistd e0 /\ lwdist Kx /\ rcompose (lwden (LA L2 a :: Kx)) (sden e0) = lwden (LA L a :: K).
Proof.
  intros HK; unfold hop_at; destruct (rev (segs_of (firstn p K))) as [|Sp rpre]; [discriminate|].
  intros H; apply first_some_in in H as [T0 H]; revert H; unfold hop_try.
  destruct (hop_prop F ntm L a p K T0) as [[[[Sp1 e] L'] Kx']|]; [|discriminate].
  destruct (hop_chk F ntm L a p K Sp1 e L' Kx') eqn:E; [|discriminate].
  intros H; injection H as <- <- <-; exact (hop_chk_sound L a p K Sp1 e L' Kx' HK E).
Qed.

Lemma hop_first_some L a K ps : forall p x, hop_first F ntm L a K ps = Some (p, x) -> hop_at F ntm L a p K = Some x.
Proof.
  induction ps as [|q r IH]; intros p x; cbn [hop_first]; [discriminate|].
  destruct (hop_at F ntm L a q K) as [y|] eqn:E; [|exact (IH p x)].
  intros H; injection H as <- <-; exact E.
Qed.

Lemma catom_sound cc (Hcc : cc_ok cc) fuel : forall L a K K', lwdist K -> catom F ntm fuel cc L a K = Some K' ->
  lwdist K' /\ lwden K' = lwden (LA L a :: K).
Proof.
  induction fuel as [|f IH]; intros L a K K' HK; cbn [catom].
  - intros H; injection H as <-; split; [constructor; [exact I|exact HK]|reflexivity].
  - destruct (hop_first F ntm L a K (seq 1 (nlead K))) as [[p [[e0 L2] Kx]]|] eqn:Eh.
    + apply hop_first_some in Eh; destruct (hop_at_sound L a p K e0 L2 Kx HK Eh) as [He0 [HKx D]].
      destruct (recons cc p Kx) as [K3|] eqn:E3; [|discriminate]; cbn [obind].
      destruct (recons_sound cc Hcc p Kx K3 HKx E3) as [HK3 D3].
      destruct (catom F ntm f cc L2 a K3) as [K4|] eqn:E4; [|discriminate]; cbn [obind]; intros H.
      destruct (IH L2 a K3 K4 HK3 E4) as [HK4 D4].
      destruct (Hcc e0 K4 K' He0 HK4 H) as [A B]; split; [exact A|].
      rewrite B, D4, <- D; cbn [Layered.lwden]; rewrite D3; reflexivity.
    + intros H; injection H as <-; split; [constructor; [exact I|exact HK]|reflexivity].
Qed.

(** *** The cons *)

Lemma front_sound cc (Hcc : cc_ok cc) s K K' : sdistd s -> lwdist K ->
  (let '(s', io) := iface F ntm s K in
   match io with
   | SNil => Some (LS s' :: K)
   | _ => obind (cc io K) (cc s')
   end) = Some K' ->
  lwdist K' /\ lwden K' = rcompose (lwden K) (sden s).
Proof.
  intros Hs HK; destruct (iface F ntm s K) as [s' io] eqn:Ei.
  destruct (iface_sound s K s' io Hs HK Ei) as [Hs' [Hio D]].
  destruct io as [|h ts m r].
  - intros H; injection H as <-; split; [constructor; assumption|].
    change (sden SNil) with (@ridentity T) in D; rewrite rcompose_identity_l in D; exact D.
  - destruct (cc (SEnt h ts m r) K) as [K1|] eqn:E1; [|discriminate]; cbn [obind]; intros H.
    destruct (Hcc _ K K1 Hio HK E1) as [H1 D1]; destruct (Hcc s' K1 K' Hs' H1 H) as [A B].
    split; [exact A|]; rewrite B, D1, <- rcompose_assoc; exact D.
Qed.

Lemma ccons_sound fuel : cc_ok (ccons F ntm fuel).
Proof.
  induction fuel as [|f IH]; intros s K K' Hs HK;
    [exact (cons_seg_sound lenv tenv aenv penv F HF ntm Hntm K s K' Hs HK)|].
  pose proof (cc0_ok _ IH) as IH0.
  cbn [ccons]; cbn zeta.
  destruct (existsb needs_split (stargets s)).
  { destruct (singles F ntm s) as [[sa tes]|] eqn:Esi; [|discriminate].
    destruct (singles_sound s sa tes Hs Esi) as [Hsa [Htes Ds]].
    assert (Hfold : forall tes0, Forall (fun te => sdistd (snd te) /\ tfront F [fst te] SNil = Some (snd te)) tes0 ->
              forall K1,
              fold_right (fun te acc => obind acc (fun K0 =>
                 match split1 F ntm (fst te) with
                 | Some (Some (E', N', rho)) =>
                     obind (match rho with SNil => Some K0 | _ => ccons F ntm f rho K0 end)
                           (fun K1 => obind (match N' with SNil => Some K1 | _ => ccons F ntm f N' K1 end) (ccons F ntm f E'))
                 | Some None => ccons F ntm f (snd te) K0
                 | None => None
                 end)) (Some K) tes0 = Some K1 ->
              lwdist K1 /\ forall X, rcompose (lwden K1) X = rcompose (lwden K) (chain tes0 X)).
    { induction tes0 as [|te r IHr]; intros HT K1; cbn [fold_right chain].
      - intros H; injection H as <-; split; [exact HK|reflexivity].
      - inversion HT as [|? ? [Hte Efr] HT']; subst.
        destruct (fold_right _ (Some K) r) as [Kr|] eqn:Er; [|discriminate]; cbn [obind].
        destruct (IHr HT' Kr eq_refl) as [HKr Dr].
        destruct (split1 F ntm (fst te)) as [[[[E' N'] rho]|]|] eqn:Esp; [| |discriminate].
        + destruct (split1_sound _ _ _ _ _ Esp Efr) as [HE [HN [Hrho D]]].
          destruct (match rho with SNil => Some Kr | _ => ccons F ntm f rho Kr end) as [Ka|] eqn:Ea; [|discriminate].
          cbn [obind].
          destruct (match N' with SNil => Some Ka | _ => ccons F ntm f N' Ka end) as [Kb|] eqn:Eb; [|discriminate].
          cbn [obind]; intros H.
          destruct (IH0 rho Kr Ka Hrho HKr Ea) as [HKa Da]; destruct (IH0 N' Ka Kb HN HKa Eb) as [HKb Db].
          destruct (IH E' Kb K1 HE HKb H) as [A B]; split; [exact A|].
          intros X; rewrite <- Dr, <- D, B, Db, Da, <- !rcompose_assoc; reflexivity.
        + intros H; destruct (IH (snd te) Kr K1 Hte HKr H) as [A B]; split; [exact A|].
          intros X; rewrite <- Dr, B, <- !rcompose_assoc; reflexivity. }
    destruct (fold_right _ (Some K) tes) as [K1|] eqn:Ef; [|discriminate]; cbn [obind]; intros H.
    destruct (Hfold tes Htes K1 Ef) as [HK1 D1].
    destruct (IH0 sa K1 K' Hsa HK1 H) as [A B]; split; [exact A|]; rewrite B, D1, Ds; reflexivity. }
  destruct K as [|[s1|L a] K0];
    [exact (cons_seg_sound lenv tenv aenv penv F HF ntm Hntm _ s K' Hs HK)| |].
  - inversion HK as [|? ? Hs1 HK0]; subst.
    destruct (negb (has_terms s) || (bound_only s1 && (no_tails s || negb (has_terms s1)))).
    { destruct (fcomp F ntm s1 s) as [s'|] eqn:E; [|discriminate].
      destruct (fcomp_ok _ _ _ Hs1 Hs E) as [Hd D].
      assert (Hgen : lwdist K' /\ lwden K' = rcompose (lwden K0) (sden s') ->
                     lwdist K' /\ lwden K' = rcompose (lwden (LS s1 :: K0)) (sden s)).
      { intros [A B]; split; [exact A|]; rewrite B, D; cbn [Layered.lwden]; rewrite rcompose_assoc; reflexivity. }
      destruct s' as [|h ts m r]; [|exact (fun H => Hgen (IH _ K0 K' Hd HK0 H))].
      intros H; injection H as <-; apply Hgen; split; [exact HK0|].
      change (sden SNil) with (@ridentity T); rewrite rcompose_identity_r; reflexivity. }
    destruct (try_join F ntm s s1 K0) as [jr|] eqn:Ej.
    { pose proof (try_join_sound s s1 K0 jr Hs HK Ej) as Ho.
      destruct jr as [c|j sa Kp|se em].
      - destruct Ho as [Hc D]; intros H; destruct (IH0 c K0 K' Hc HK0 H) as [A B].
        split; [exact A|]; rewrite B; exact D.
      - destruct Ho as [Hsa [HKp D]].
        destruct Kp as [|[p1|? ?] Kp']; try discriminate.
        inversion HKp as [|? ? Hp1 HKp']; subst.
        destruct (fcomp F ntm p1 sa) as [sm|] eqn:Em; [|discriminate]; intros H.
        destruct (fcomp_ok _ _ _ Hp1 Hsa Em) as [Hsm Dm].
        assert (Hl : lwdist (LS sm :: Kp')) by (constructor; assumption).
        destruct (rr_up_sound j _ Hl) as [Hu Du].
        destruct (rr_up F ntm j (LS sm :: Kp')) as [|[x|? ?] r]; try discriminate.
        inversion Hu as [|? ? Hx Hr]; subst.
        destruct (sweep_sound _ IH j x r K' Hx Hr H) as [A B]; split; [exact A|].
        cbn [Layered.lwden] in Du; rewrite B, Du, Dm, rcompose_assoc; exact D.
      - destruct Ho as [Hsa [Hem D]].
        destruct (ccons F ntm f em (LS s1 :: K0)) as [K1|] eqn:E1; [|discriminate]; cbn [obind]; intros H.
        destruct (IH em _ K1 Hem HK E1) as [H1 D1]; destruct (IH se K1 K' Hsa H1 H) as [A B].
        split; [exact A|]; rewrite B, D1, <- rcompose_assoc, D; reflexivity. }
    destruct (try_swap F ntm s s1 (LS s1 :: K0) K0) as [[[[sa f1] n] rho]|] eqn:Esw.
    { unfold try_swap in Esw; destruct (named_term s1); [discriminate|].
      destruct (has_terms s1); [|discriminate]; destruct (above F (LS s1 :: K0) K0); [discriminate|].
      destruct (swap_sound s s1 sa f1 n rho Hs Hs1 Esw) as [Hsa [Hf [Hn [Hr D]]]].
      destruct (ccons F ntm f rho K0) as [X|] eqn:E1; [|discriminate]; cbn [obind].
      destruct (ccons F ntm f n X) as [K1|] eqn:E2; [|discriminate]; cbn [obind].
      destruct (ccons F ntm f f1 K1) as [K2|] eqn:E3; [|discriminate]; cbn [obind]; intros H.
      destruct (IH rho K0 X Hr HK0 E1) as [HX DX]; destruct (IH n X K1 Hn HX E2) as [H1 D1].
      destruct (IH f1 K1 K2 Hf H1 E3) as [H2 D2]; destruct (IH sa K2 K' Hsa H2 H) as [A B].
      split; [exact A|]; rewrite B, D2, D1, DX; cbn [Layered.lwden].
      rewrite <- (rcompose_assoc (lwden K0) (sden s1) (sden s)), <- D, !rcompose_assoc; reflexivity. }
    exact (front_sound _ IH s _ K' Hs HK).
  - inversion HK as [|? ? _ HK0]; subst.
    destruct (has_terms s); [exact (front_sound _ IH s _ K' Hs HK)|].
    destruct (wcomp F ntm (WAtom SNil L a (WEnd SNil)) (WEnd s)) as [[s0|sq L' a' [U|s2 L2 a2 w2]]|] eqn:E;
      [intros H; discriminate H| |intros H; discriminate H|intros H; discriminate H].
    assert (Hw1 : wdist (WAtom SNil L a (WEnd SNil))) by (split; exact I).
    destruct (wcomp_sound lenv tenv aenv penv F HF ntm Hntm (WAtom SNil L a (WEnd SNil)) (WEnd s) _ Hw1 Hs E)
      as [[Hd' HdU] D].
    match goal with |- obind ?X _ = _ -> _ => destruct X as [K1|] eqn:E1; [|discriminate] end.
    cbn [obind]; intros H; injection H as <-; destruct (IH0 sq K0 K1 Hd' HK0 E1) as [HK1 DK1].
    split; [apply lwdist_lpre; [exact HdU|constructor; [exact I|exact HK1]]|].
    rewrite lwden_lpre; cbn [Layered.lwden]; rewrite DK1.
    rewrite !wden_atom in D.
    change (Normalise.sden lenv tenv aenv penv SNil) with (@ridentity T) in D.
    change (Normalise.wden lenv tenv aenv penv (WEnd SNil)) with (@ridentity T) in D.
    change (Normalise.wden lenv tenv aenv penv (WEnd U)) with (sden U) in D.
    change (Normalise.wden lenv tenv aenv penv (WEnd s)) with (sden s) in D.
    rewrite rcompose_identity_l, rcompose_identity_r in D.
    rewrite <- !rcompose_assoc, D; reflexivity.
Qed.

Lemma canon_f_sound fuel l : forall l', lwdist l -> canon_f F ntm fuel l = Some l' -> lwdist l' /\ lwden l' = lwden l.
Proof.
  induction l as [|[s|L a] r IH]; intros l' Hl; cbn [canon_f].
  - intros H; injection H as <-; auto.
  - inversion Hl as [|? ? Hs Hr]; subst.
    destruct (canon_f F ntm fuel r) as [r'|] eqn:E; [|discriminate]; cbn [obind]; intros H.
    destruct (IH r' Hr eq_refl) as [H1 D1]; destruct (ccons_sound _ s r' l' Hs H1 H) as [A B].
    split; [exact A|]; rewrite B, D1; reflexivity.
  - inversion Hl as [|? ? Hs Hr]; subst.
    destruct (canon_f F ntm fuel r) as [r'|] eqn:E; [|discriminate]; cbn [obind]; intros H.
    destruct (IH r' Hr eq_refl) as [H1 D1].
    destruct (catom_sound _ (ccons_sound fuel) fuel L a r' l' H1 H) as [A B].
    split; [exact A|]; rewrite B; cbn [Layered.lwden]; rewrite D1; reflexivity.
Qed.

Theorem canon_sound l l' : lwdist l -> canon F ntm l = Some l' -> lwdist l' /\ lwden l' = lwden l.
Proof. apply canon_f_sound. Qed.

End Sound.
