(** * The canonical layered word

    [Layered.fold] returns a layered word that means what the expression
    means.  [canon] puts it in canonical form, one step at a time from
    the end: [ccons s K] is the canonical word of [s] followed by the
    canonical word [K].

    For a segment [s] with terms in front of [K = s1 :: K']:

    - when [s1] does nothing to named variables that the rest can tell
      from the identity, the terms of [s] have the payload of some later
      layer and join it, carried there by bound variables ([thread]);
    - when the terms of [s1] are all on bound variables, the two layers
      do not see each other, and the order between their payloads
      ([above]) decides which goes first; [s] goes behind [s1] by an
      inverse of what [s1] does to named variables ([sinv]);
    - otherwise [s] is a new first layer, and the variables between it
      and [s1] are put in canonical form ([iface]): each goes on as the
      least variable with the same target in [s1], bound variables that
      nothing reaches are dropped, and the rest are numbered in the
      order they are first used. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Layered.
Import ListNotations.

Section Canon.

Variable F : order.
Variable ntm : nat.

(** ** Segments as lists of entries *)

Fixpoint ents (s : seg) : list (lexp * tlist * nat) :=
  match s with SNil => [] | SEnt h ts m r => (h, ts, m) :: ents r end.

Definition bent (s : seg) : tlist * nat := match sfind F LNone s with Some e => ofe e | None => (TNil, 0) end.

Definition mkseg (es : list (lexp * tlist * nat)) : option seg :=
  fold_right (fun '(h, ts, m) acc => obind acc (sset F h ts m)) (Some SNil) es.

Definition vars (l : list (lexp * nat)) : tlist := tl_of (map (fun v => NVar (fst v) (snd v)) l).
Definition bvars (l : list nat) : tlist := tl_of (map (NVar LNone) l).

Definition mem (j : nat) (l : list nat) : bool := existsb (Nat.eqb j) l.

(** ** The variables between two segments

    Every variable; through an atom, the ones its lifts pass around. *)
Definition lim_t := lexp -> option nat.
Definition nolim : lim_t := fun _ => None.
Definition within (lim : lim_t) (v : lexp * nat) : bool :=
  match lim (fst v) with Some c => snd v <? c | None => true end.

(** The bound variables a segment sends something to. *)
Fixpoint bhits (ts : list ntgt) : list nat :=
  match ts with
  | [] => []
  | NVar LNone j :: r => j :: bhits r
  | NVar _ _ :: r => bhits r
  | NBind _ (WEnd ps) (Some _) :: r =>
      (fix go (l : list ntgt) : list nat :=
         match l with NVar LNone j :: l' => j :: go l' | _ :: l' => go l' | [] => [] end) (stargets ps) ++ bhits r
  | NBind _ _ _ :: r => bhits r
  end.

Definition dead (lim : lim_t) (s : seg) : list nat :=
  let h := bhits (stargets s) in
  filter (fun j => negb (mem j h) && within lim (LNone, j)) (seq 0 (snd (bent s))).

(** Dropping them: [s] re-indexed, and the next segment without those inputs. *)
Definition prune (lim : lim_t) (s s1 : seg) : option (seg * seg) :=
  match dead lim s with
  | [] => Some (s, s1)
  | D =>
      let M := snd (bent s) in
      let c := fun i => i - List.length (filter (fun d => d <? i) D) in
      match mkseg [(LNone, bvars (map c (seq 0 M)), M - List.length D)],
            mkseg [(LNone, bvars (filter (fun j => negb (mem j D)) (seq 0 M)), M)] with
      | Some pi, Some iota =>
          match scomp F ntm pi s, scomp F ntm s1 iota with Some s', Some s1' => Some (s', s1') | _, _ => None end
      | _, _ => None
      end
  end.

(** The order on variables: by label, then index. *)
Definition vless (a b : lexp * nat) : bool :=
  match lcmp F (fst a) (fst b) with Some Lt => true | Some Eq => snd a <? snd b | _ => false end.

Definition vmin (l : list (lexp * nat)) : option (lexp * nat) :=
  fold_right (fun v acc => match acc with None => Some v | Some w => if vless v w then Some v else Some w end) None l.

Fixpoint findix (t : ntgt) (ts : tlist) (k : nat) : list nat :=
  match ts with TNil => [] | TCons t' r => (if ntgt_eqb t t' then [k] else []) ++ findix t r (S k) end.

(** The named inputs of [s1] with the target [t]. *)
Definition named_srcs (s1 : seg) (t : ntgt) : list (lexp * nat) :=
  flat_map (fun '(h, ts, m) => match h with LNone => [] | _ => map (fun k => (h, k)) (findix t ts 0) end) (ents s1)
  ++ match t with
     | NVar LNone _ => []
     | NVar g i =>
         match sfind F g s1 with
         | Some (Some (ts, m)) => if m <=? i then [(g, i - m + tlen ts)] else []
         | Some None => [(g, i)]
         | None => []
         end
     | _ => []
     end.

Definition veqb (a b : lexp * nat) : bool := lexp_eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

(** The representative of an input of [s1]: the least named input with
    the same target, else the least bound one. *)
Definition rep_of (lim : lim_t) (s1 : seg) (v : lexp * nat) : lexp * nat :=
  match seg_tgt F s1 (fst v) (snd v) with
  | Some t =>
      match vmin (filter (within lim) (named_srcs s1 t)) with
      | Some w => w
      | None => match filter (fun k => within lim (LNone, k)) (findix t (fst (bent s1)) 0) with
                | k :: _ => (LNone, k)
                | [] => v
                end
      end
  | None => v
  end.

(** The inputs that may not be their own representative. *)
Definition cands (s1 : seg) : list (lexp * nat) :=
  flat_map (fun '(h, ts, m) => map (fun k => (h, k)) (seq 0 (tlen ts))) (ents s1)
  ++ flat_map (fun t => match t with
                        | NVar g i => match sfind F g s1 with
                                      | Some (Some (ts, m)) => if m <=? i then [(g, i - m + tlen ts)] else []
                                      | Some None => [(g, i)]
                                      | None => []
                                      end
                        | _ => [] end) (stargets s1).

Definition kmap (lim : lim_t) (s1 : seg) : list ((lexp * nat) * (lexp * nat)) :=
  filter (fun p => negb (veqb (fst p) (snd p))) (map (fun v => (v, rep_of lim s1 v)) (filter (within lim) (cands s1))).

Fixpoint klabs (km : list ((lexp * nat) * (lexp * nat))) (seen : list lexp) : list lexp :=
  match km with
  | [] => []
  | ((g, _), _) :: r => if existsb (lexp_eqb g) seen then klabs r seen else g :: klabs r (g :: seen)
  end.

Definition kseg (km : list ((lexp * nat) * (lexp * nat))) : option seg :=
  mkseg (map (fun g =>
           let mine := filter (fun p => lexp_eqb (fst (fst p)) g) km in
           let I := fold_right (fun p a => Nat.max (S (snd (fst p))) a) 0 mine in
           let tg := fun k => match find (fun p => Nat.eqb (snd (fst p)) k) mine with
                              | Some (_, w) => w | None => (g, k) end in
           (g, vars (map tg (seq 0 I)), I)) (klabs km [])).

(** Terms with the identity payload keep it: the kernel map does not
    change what the rest does to their names. *)
Fixpoint pure_ts (ts : tlist) : tlist :=
  match ts with
  | TNil => TNil
  | TCons (NBind u (WEnd _) None) r => TCons (NBind u (WEnd SNil) None) (pure_ts r)
  | TCons t r => TCons t (pure_ts r)
  end.

Definition repure (s : seg) : option seg := mkseg (map (fun '(h, ts, m) => (h, pure_ts ts, m)) (ents s)).

Definition reroute (lim : lim_t) (s s1 : seg) : option seg :=
  match kmap lim s1 with
  | [] => Some s
  | km => obind (kseg km) (fun kap => obind (scomp F ntm kap s) repure)
  end.

(** Bound variables below the default region, in the order they are
    first used. *)
Fixpoint nodup_nat (l : list nat) (seen : list nat) : list nat :=
  match l with [] => [] | x :: r => if mem x seen then nodup_nat r seen else x :: nodup_nat r (x :: seen) end.

Fixpoint index_of (x : nat) (l : list nat) (k : nat) : nat :=
  match l with [] => k | y :: r => if Nat.eqb x y then k else index_of x r (S k) end.

Definition renumber (lim : lim_t) (s s1 : seg) : option (seg * seg) :=
  let M := match lim LNone with Some c => Nat.min c (snd (bent s)) | None => snd (bent s) end in
  let ord := nodup_nat (filter (fun j => j <? M) (bhits (stargets s))) [] in
  if list_eq_dec Nat.eq_dec ord (seq 0 (List.length ord)) then Some (s, s1)
  else if negb (Nat.eqb (List.length ord) M) then Some (s, s1)
  else match mkseg [(LNone, bvars (map (fun j => index_of j ord 0) (seq 0 M)), M)], mkseg [(LNone, bvars ord, M)] with
       | Some p, Some q =>
           match scomp F ntm p s, scomp F ntm s1 q with Some s', Some s1' => Some (s', s1') | _, _ => None end
       | _, _ => None
       end.

Definition iface (lim : lim_t) (s s1 : seg) : option (seg * seg) :=
  obind (reroute lim s s1) (fun sa => obind (prune lim sa s1) (fun '(sb, s1b) => renumber lim sb s1b)).

(** The two segments after [iface], when they compose to what the two
    before compose to; otherwise unchanged. *)
Definition pair_ok (s s1 s' s1' : seg) : bool :=
  match scomp F ntm s1 s, scomp F ntm s1' s' with Some c1, Some c2 => seg_eqb c1 c2 | _, _ => false end.

Definition iface_c (s s1 : seg) : seg * seg :=
  match iface nolim s s1 with
  | Some (s', s1') => if pair_ok s s1 s' s1' then (s', s1') else (s, s1)
  | None => (s, s1)
  end.

(** ** Joining a later layer *)

(** [sig] is what the steps passed so far do to named variables.  The
    layer found is the first whose rest cannot tell it from the
    identity. *)
Definition same_rest (sg : seg) (K : lword) : bool :=
  match sg, K with
  | SNil, _ => true
  | _, LS s2 :: _ =>
      match scomp F ntm s2 sg with Some c => seg_eqb (sdrop_none c) (sdrop_none s2) | None => false end
  | _, _ => false
  end.

Fixpoint scan (sig : seg) (K : lword) (j : nat) : option nat :=
  match K with
  | LS s1 :: K' =>
      match scomp F ntm s1 sig with
      | Some c => let sg := sdrop_none c in
                  if has_terms sg then None
                  else if same_rest sg K' then (if has_terms s1 then Some (S j) else None)
                  else scan sg K' (S j)
      | None => None
      end
  | _ => None
  end.

(** The terms of a segment replaced by the bound variables [0 ..], the
    other bound targets moved up. *)
Fixpoint rterms (ts : tlist) (k : nat) : tlist * list ntgt :=
  match ts with
  | TNil => (TNil, [])
  | TCons (NBind u w b) r => let '(r', T) := rterms r (S k) in (TCons (NVar LNone k) r', NBind u w b :: T)
  | TCons t r => let '(r', T) := rterms r k in (TCons t r', T)
  end.

Fixpoint rents (es : list (lexp * tlist * nat)) (k : nat) : list (lexp * tlist * nat) * list ntgt :=
  match es with
  | [] => ([], [])
  | (h, ts, m) :: r =>
      let '(ts', T) := rterms ts k in
      let '(r', T') := rents r (k + List.length T) in
      ((h, ts', m) :: r', T ++ T')
  end.

Definition nterms (s : seg) : nat := List.length (filter is_term (stargets s)).

Definition tfront (T : list ntgt) (s : seg) : option seg :=
  fold_right (fun t acc => obind acc (sfront F LNone t)) (Some s) T.

Definition is_pure (t : ntgt) : bool := match t with NBind _ (WEnd SNil) None => true | _ => false end.

(** [s] as its renaming [sa] followed by its terms on bound variables. *)
Definition unterm (s : seg) : option (seg * list ntgt) :=
  match scomp F ntm (shseg LNone (nterms s)) s with
  | Some s1 =>
      let '(es, T) := rents (ents s1) 0 in
      match mkseg es, tfront T SNil with
      | Some sa, Some eT =>
          match scomp F ntm eT sa with
          | Some s2 => if seg_eqb s2 s && forallb is_pure T then Some (sa, T) else None
          | None => None
          end
      | _, _ => None
      end
  | None => None
  end.

Fixpoint thread (j : nat) (T : list ntgt) (K : lword) : option lword :=
  match j, K with
  | 1, LS s1 :: K' => option_map (fun x => LS x :: K') (tfront T s1)
  | S j', LS s1 :: K' =>
      match slifts F ntm (List.length T) s1, thread j' T K' with
      | Some a, Some b => Some (LS a :: b)
      | _, _ => None
      end
  | _, _ => None
  end.

Definition named_term (s : seg) : bool := has_terms (sdrop_none s).

(** ** Going behind the first layer *)

(** An inverse of a renaming of named variables; named outputs that
    nothing is sent to come back from fresh bound variables [R]. *)
Definition sinv (sg : seg) : option (seg * list ntgt) :=
  fold_right (fun '(g, ts, m) acc =>
    obind acc (fun '(a, R) =>
      let pre := map (fun i => (i, vmin (named_srcs sg (NVar g i)))) (seq 0 m) in
      let miss := filter (fun p => match snd p with None => true | _ => false end) pre in
      let tg := fun p => match snd p with
                         | Some (h, k) => NVar h k
                         | None => NVar LNone (List.length R + index_of (fst p) (map fst miss) 0)
                         end in
      match sset F g (tl_of (map tg pre)) (tlen ts) a with
      | Some a' => Some (a', R ++ map (fun p => NVar g (fst p)) miss)
      | None => None
      end)) (Some (SNil, [])) (ents sg).

(** ** The order between payloads

    The height of a payload (how deep the terms it sends variables to
    go), then what it does to each variable, in the order of the
    variables. *)
Fixpoint lfollow (l : lword) (h : lexp) (i : nat) : option (ntgt * nat) :=
  match l with
  | [] => Some (NVar h i, 0)
  | LS s :: r =>
      match seg_tgt F s h i with
      | Some (NVar g j) => lfollow r g j
      | Some t => Some (t, List.length r)
      | None => None
      end
  | LA L a :: r =>
      match wtgt F (WAtom SNil L a (WEnd SNil)) h i with
      | Some (NVar g j) => lfollow r g j
      | _ => None
      end
  end.

Inductive hres := HVar (g : lexp) (i : nat) | HTerm (u : nat) (b : option nat) (d : nat) | HStuck.

Definition follow (l : lword) (g : lexp) (i : nat) : hres :=
  match lfollow l g i with
  | Some (NVar g' j, _) => HVar g' j
  | Some (NBind u _ b, d) => HTerm u b d
  | None => HStuck
  end.

Definition lcmp3 (a b : lexp) : comparison := match lcmp F a b with Some c => c | None => Eq end.

Definition hcmp (x y : hres) : comparison :=
  match x, y with
  | HVar g i, HVar g' i' => match lcmp3 g g' with Eq => Nat.compare i i' | c => c end
  | HVar _ _, _ => Lt
  | _, HVar _ _ => Gt
  | HTerm u b d, HTerm u' b' d' =>
      match Nat.compare u u' with
      | Eq => match Nat.compare d d' with
              | Eq => match b, b' with
                      | Some n, Some n' => Nat.compare n n'
                      | None, Some _ => Lt
                      | Some _, None => Gt
                      | None, None => Eq
                      end
              | c => c
              end
      | c => c
      end
  | HTerm _ _ _, HStuck => Lt
  | HStuck, HTerm _ _ _ => Gt
  | HStuck, HStuck => Eq
  end.

Fixpoint lexc (a b : list hres) : comparison :=
  match a, b with
  | x :: a', y :: b' => match hcmp x y with Eq => lexc a' b' | c => c end
  | _, _ => Eq
  end.

Fixpoint linsert (g : lexp) (l : list lexp) : list lexp :=
  match l with
  | [] => [g]
  | h :: r => match lcmp F g h with Some Lt => g :: l | Some Eq => l | _ => h :: linsert g r end
  end.

Definition wlabs (l : lword) : list lexp :=
  fold_right (fun x acc =>
    match x with
    | LS sg => fold_right (fun '(g, _, _) a => match g with LNone => a | _ => linsert g a end) acc (ents sg)
    | _ => acc
    end) [] l.

Definition wbound (l : lword) : nat :=
  fold_right (fun x acc => match x with LS sg => List.length (stargets sg) + acc | _ => acc end) 2 l.

Definition headv (labs : list lexp) (N : nat) (l : lword) : list hres :=
  flat_map (fun g => map (follow l g) (seq 0 N)) labs.

(** The heights of every rest of the word, the word itself first. *)
Fixpoint hts (labs : list lexp) (N : nat) (l : lword) : list nat :=
  match l with
  | [] => [0]
  | x :: r =>
      let H := hts labs N r in
      fold_right (fun h acc => match h with
                               | HTerm _ _ d => Nat.max acc (S (nth (List.length H - 1 - d) H 0))
                               | _ => acc
                               end) 0 (headv labs N (x :: r)) :: H
  end.

(** The payload [K] is above the payload [K'] (its rest). *)
Definition above (K K' : lword) : bool :=
  let labs := wlabs K in
  let N := wbound K in
  let H := hts labs N K in
  match Nat.compare (nth 0 H 0) (nth 1 H 0) with
  | Gt => true
  | Lt => false
  | Eq => match lexc (headv labs N K) (headv labs N K') with Lt => false | _ => true end
  end.

(** The four segments [sa; f1; n; rho] that [s; s1] becomes when [s]
    goes behind [s1], when they compose to the same. *)
Definition swap (s s1 : seg) : option (seg * seg * seg * seg) :=
  let sg1 := sdrop_none s1 in
  match sinv sg1, unterm s with
  | Some (nu, R), Some (sa, T) =>
      match slifts F ntm (List.length T) s1, obind (sset F LNone TNil (List.length R) nu) (tfront T),
            sset F LNone (tl_of R) 0 sg1 with
      | Some f1, Some n, Some rho =>
          match scomp F ntm s1 s, obind (obind (scomp F ntm f1 sa) (scomp F ntm n)) (scomp F ntm rho) with
          | Some c1, Some c2 => if seg_eqb c1 c2 then Some (sa, f1, n, rho) else None
          | _, _ => None
          end
      | _, _, _ => None
      end
  | _, _ => None
  end.

(** ** The canonical cons *)

Fixpoint recons (cc : seg -> lword -> option lword) (n : nat) (l : lword) : option lword :=
  match n, l with
  | 0, _ => Some l
  | S n', LS x :: l' => obind (recons cc n' l') (cc x)
  | _, _ => None
  end.

Fixpoint ccons (fuel : nat) (s : seg) (K : lword) : option lword :=
  match fuel with
  | 0 => cons_seg F ntm s K
  | S f =>
      match K with
      | LS s1 :: K' =>
          if negb (has_terms s) || (bound_only s1 && no_atoms s) then
            match scomp F ntm s1 s with
            | Some SNil => Some K'
            | Some s' => ccons f s' K'
            | None => None
            end
          else
            match (if named_term s1 then None
                   else match scan SNil K 0 with
                        | Some j => obind (unterm s) (fun '(sa, T) => obind (thread j T K) (fun Kp => Some (j, sa, Kp)))
                        | None => None
                        end) with
            | Some (j, sa, Kp) => obind (recons (ccons f) j Kp) (ccons f sa)
            | None =>
                match (if named_term s1 || negb (has_terms s1) || above K K' then None else swap s s1) with
                | Some (sa, f1, n, rho) =>
                    obind (ccons f rho K') (fun X => obind (ccons f n X) (fun K1 => obind (ccons f f1 K1) (ccons f sa)))
                | None =>
                    let '(s', s1') := iface_c s s1 in
                    if seg_eqb s1 s1' then Some (LS s' :: K)
                    else match s1' with
                         | SNil => ccons f s' K'
                         | _ => obind (ccons f s1' K') (ccons f s')
                         end
                end
            end
      | _ => cons_seg F ntm s K
      end
  end.

Fixpoint canon (l : lword) : option lword :=
  match l with
  | [] => Some []
  | LS s :: r => obind (canon r) (ccons (4 * List.length l + 100) s)
  | LA L a :: r => option_map (cons (LA L a)) (canon r)
  end.

End Canon.
