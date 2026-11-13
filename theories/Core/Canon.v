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

(** ** Composing sorted segments

    [Normalise.scomp] puts each entry of the first segment applied into
    the other one by one.  When both are sorted this is a merge. *)
Definition mkent (h : lexp) (ts : tlist) (m : nat) (r : seg) : seg :=
  match trim h (rev (tl_list ts)) m with
  | ([], 0) => r
  | (rts, m') => SEnt h (tl_of (rev rts)) m' r
  end.

Definition comb (ts' : tlist) (m : nat) (tsS : tlist) (mS : nat) : tlist * nat :=
  (tcat ts' (tskip m tsS), if tlen tsS <=? m then m - tlen tsS + mS else mS).

Fixpoint smerge (S0 U cur : seg) {struct U} : option seg :=
  match U with
  | SNil => Some cur
  | SEnt h ts m r =>
      match tlapp F ntm S0 ts with
      | None => None
      | Some ts' =>
          (fix adv (cur : seg) : option seg :=
             match cur with
             | SNil => let '(x, k) := comb ts' m TNil 0 in option_map (mkent h x k) (smerge S0 r SNil)
             | SEnt g tsg mg rc =>
                 match lcmp F h g with
                 | Some Lt => let '(x, k) := comb ts' m TNil 0 in option_map (mkent h x k) (smerge S0 r cur)
                 | Some Eq => let '(x, k) := comb ts' m tsg mg in option_map (mkent h x k) (smerge S0 r rc)
                 | Some Gt => option_map (SEnt g tsg mg) (adv rc)
                 | None => None
                 end
             end) cur
      end
  end.

Fixpoint sortb (s : seg) : bool :=
  match s with
  | SNil => true
  | SEnt h _ _ r =>
      match r with
      | SNil => true
      | SEnt g _ _ _ => match lcmp F h g with Some Lt => sortb r | _ => false end
      end
  end.

Definition fcomp (S U : seg) : option seg :=
  if sortb S && sortb U then smerge S U S else scomp F ntm S U.

(** ** Distinct labels, checked

    The segments computed below are compared with what they replace by
    composing; for that their entries must have distinct labels, which
    holds when each label is known to be below the ones after it. *)
Fixpoint tdistb (t : ntgt) : bool :=
  match t with NVar _ _ => true | NBind _ w _ => wdistb w end
with tldistb (ts : tlist) : bool :=
  match ts with TNil => true | TCons t r => tdistb t && tldistb r end
with sdistb (s : seg) : bool :=
  match s with
  | SNil => true
  | SEnt h ts _ r =>
      match r with
      | SNil => tldistb ts
      | SEnt g _ _ _ => match lcmp F h g with Some Lt => tldistb ts && sdistb r | _ => false end
      end
  end
with wdistb (w : word) : bool :=
  match w with WEnd s => sdistb s | WAtom s _ _ w' => sdistb s && wdistb w' end.

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
          match fcomp pi s, fcomp s1 iota with Some s', Some s1' => Some (s', s1') | _, _ => None end
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
  | km => obind (kseg km) (fun kap => obind (fcomp kap s) repure)
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
           match fcomp p s, fcomp s1 q with Some s', Some s1' => Some (s', s1') | _, _ => None end
       | _, _ => None
       end.

Definition iface (lim : lim_t) (s s1 : seg) : option (seg * seg) :=
  obind (reroute lim s s1) (fun sa => obind (prune lim sa s1) (fun '(sb, s1b) => renumber lim sb s1b)).

(** The two segments after [iface], when they compose to what the two
    before compose to; otherwise unchanged. *)
Definition pair_ok (s s1 s' s1' : seg) : bool :=
  match fcomp s1 s, fcomp s1' s' with Some c1, Some c2 => seg_eqb c1 c2 | _, _ => false end.

Definition iface_c (s s1 : seg) : seg * seg :=
  match iface nolim s s1 with
  | Some (s', s1') => if pair_ok s s1 s' s1' && sdistb s' && sdistb s1' then (s', s1') else (s, s1)
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
      match fcomp s2 sg with Some c => seg_eqb (sdrop_none c) (sdrop_none s2) | None => false end
  | _, _ => false
  end.

Fixpoint scan (sig : seg) (K : lword) (j : nat) : option nat :=
  match K with
  | LS s1 :: K' =>
      match fcomp s1 sig with
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

Definition is_pure (t : ntgt) : bool := match t with NBind u (WEnd SNil) None => u <? ntm | _ => false end.

(** [s] as its renaming [sa] followed by its terms on bound variables. *)
Definition unterm (s : seg) : option (seg * list ntgt) :=
  match fcomp (shseg LNone (nterms s)) s with
  | Some s1 =>
      let '(es, T) := rents (ents s1) 0 in
      match mkseg es, tfront T SNil with
      | Some sa, Some eT =>
          match fcomp eT sa with
          | Some s2 => if seg_eqb s2 s && forallb is_pure T && sdistb sa then Some (sa, T) else None
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
          match fcomp s1 s, obind (obind (fcomp f1 sa) (fcomp n)) (fcomp rho) with
          | Some c1, Some c2 => if seg_eqb c1 c2 && sdistb n && sdistb rho then Some (sa, f1, n, rho) else None
          | _, _ => None
          end
      | _, _, _ => None
      end
  | _, _ => None
  end.

(** ** The canonical cons *)

Definition reroute_c (s s1 : seg) : seg :=
  match reroute nolim s s1 with
  | Some s' => if pair_ok s s1 s' s1 && sdistb s' then s' else s
  | None => s
  end.

(** Sending variables to their representatives, for the first [n]
    segments, from the last of them: what a segment's variables go on as
    decides which of its own inputs have the same target. *)
Fixpoint rr_up (n : nat) (l : lword) : lword :=
  match n, l with
  | S n', LS x :: r =>
      let r' := rr_up n' r in
      match r' with LS y :: _ => LS (reroute_c x y) :: r' | _ => LS x :: r' end
  | _, _ => l
  end.

(** After a join the segments passed have a new bound variable each:
    the variables between them are put in canonical form from the front,
    [n] segments deep, and what follows is consed as usual. *)
Fixpoint sweep (cc : seg -> lword -> option lword) (n : nat) (s : seg) (K : lword) : option lword :=
  match n, K with
  | S n', LS s1 :: K' =>
      let '(s', s1') := iface_c s s1 in
      match s1' with
      | SNil => cc s' K'
      | _ => if has_terms s1' then option_map (cons (LS s')) (sweep cc n' s1' K')
             else obind (cc s1' K') (cc s')
      end
  | _, _ => cc s K
  end.

Definition try_join (s s1 : seg) (K : lword) : option (nat * seg * lword) :=
  if named_term s1 then None
  else match scan SNil K 0 with
       | Some j => obind (unterm s) (fun '(sa, T) => obind (thread j T K) (fun Kp => Some (j, sa, Kp)))
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
      match K with
      | LS s1 :: K' =>
          if negb (has_terms s) || (bound_only s1 && no_atoms s) then
            match fcomp s1 s with
            | Some SNil => Some K'
            | Some s' => ccons f s' K'
            | None => None
            end
          else
            match try_join s s1 K with
            | Some (j, sa, Kp) =>
                match Kp with
                | LS p1 :: Kp' =>
                    match fcomp p1 sa with
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

Fixpoint canon_f (fuel : nat) (l : lword) : option lword :=
  match l with
  | [] => Some []
  | LS s :: r => obind (canon_f fuel r) (ccons fuel s)
  | LA L a :: r => option_map (cons (LA L a)) (canon_f fuel r)
  end.

Definition canon (l : lword) : option lword := canon_f (4 * List.length l + 100) l.

End Canon.

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
Local Notation sdistd := (sdistd lenv).
Local Notation tdist := (tdist lenv).
Local Notation tldist := (tldist lenv).
Local Notation wdist := (wdist lenv).
Local Notation lwden := (lwden lenv tenv aenv penv).
Local Notation lwdist := (lwdist lenv).


(** *** The merge *)

Local Notation esem := (esem lenv tenv aenv penv).

Fixpoint below (l : option label) (s : seg) : Prop :=
  match s with SNil => True | SEnt h _ _ r => olabel_lt l (lden h) /\ below l r end.

Fixpoint sorted (s : seg) : Prop :=
  match s with SNil => True | SEnt h _ _ r => below (lden h) r /\ sorted r end.

Lemma below_get l s : below l s -> sget lenv l s = None.
Proof.
  induction s as [|h ts m r IH] using seg_spine; [reflexivity|]; intros [H1 H2]; cbn [sget].
  destruct (label_eqb (lden h) l) eqn:E; [apply label_eqb_eq in E; subst; destruct (olabel_lt_irrefl _ H1)|exact (IH H2)].
Qed.

Lemma below_trans a b s : olabel_lt a b -> below b s -> below a s.
Proof.
  intros Hab; induction s as [|h ts m r IH] using seg_spine; [exact (fun H => H)|]; intros [H1 H2].
  split; [exact (olabel_lt_trans _ _ _ Hab H1)|exact (IH H2)].
Qed.

Lemma sortb_sound s : sortb F s = true -> sorted s.
Proof.
  induction s as [|h ts m r IH] using seg_spine; [intros _; exact I|]; cbn [sortb].
  destruct r as [|g tsg mg r']; [intros _; split; exact I|].
  destruct (lcmp F h g) as [[| |]|] eqn:E; try discriminate; intros H.
  pose proof (lcmp_sound lenv F HF _ _ _ E) as Hlt; cbn in Hlt.
  destruct (IH H) as [Hb Hs]; split; [|exact (conj Hb Hs)].
  split; [exact Hlt|exact (below_trans _ _ _ Hlt Hb)].
Qed.

Lemma distb_sound :
  (forall t, tdistb F t = true -> tdist t) /\ (forall ts, tldistb F ts = true -> tldist ts)
  /\ (forall s, sdistb F s = true -> sdistd s /\ sorted s) /\ (forall w, wdistb F w = true -> wdist w).
Proof.
  apply nf_mind.
  - intros h i _; exact I.
  - intros u w IH b H; exact (IH H).
  - intros _; exact I.
  - intros t IHt r IHr H; cbn [tldistb] in H; apply andb_true_iff in H as [H1 H2]; split; [exact (IHt H1)|exact (IHr H2)].
  - intros _; split; exact I.
  - intros h ts IHts m r IHr H; cbn [sdistb] in H.
    destruct r as [|g tsg mg r'].
    + split; [exact (conj eq_refl (conj (IHts H) I))|split; exact I].
    + destruct (lcmp F h g) as [[| |]|] eqn:E; try discriminate.
      apply andb_true_iff in H as [H1 H2]; destruct (IHr H2) as [Hd [Hb Hs]].
      pose proof (lcmp_sound lenv F HF _ _ _ E) as Hlt; cbn in Hlt.
      assert (Hbl : below (lden h) (SEnt g tsg mg r')) by (split; [exact Hlt|exact (below_trans _ _ _ Hlt Hb)]).
      split; [exact (conj (below_get _ _ Hbl) (conj (IHts H1) Hd))|exact (conj Hbl (conj Hb Hs))].
  - intros s IH H; exact (proj1 (IH H)).
  - intros s IHs L a w IHw H; cbn [wdistb] in H; apply andb_true_iff in H as [H1 H2]; split; [exact (proj1 (IHs H1))|exact (IHw H2)].
Qed.

Lemma sdistb_sound s : sdistb F s = true -> sdistd s.
Proof. intros H; exact (proj1 (proj1 (proj2 (proj2 distb_sound)) s H)). Qed.

Lemma mkent_spec h ts m r : below (lden h) r ->
  (forall l j, esem l (sget lenv l (mkent h ts m r)) j
               = if label_eqb (lden h) l then esem l (Some (ts, m)) j else esem l (sget lenv l r) j)
  /\ (forall b, olabel_lt b (lden h) -> below b r -> below b (mkent h ts m r))
  /\ (sorted r -> sorted (mkent h ts m r))
  /\ (sdistd r -> tldist ts -> sdistd (mkent h ts m r)).
Proof.
  intros Hb; unfold mkent; destruct (trim h (rev (tl_list ts)) m) as [rts m'] eqn:Et.
  assert (Hsem : forall j, esem (lden h) (Some (ts, m)) j = esem (lden h) (Some (tl_of (rev rts), m')) j).
  { intros j; rewrite !(esem_lsem lenv tenv aenv penv), tl_list_of; rewrite <- (rev_involutive (tl_list ts)) at 1.
    apply (trim_sound lenv tenv aenv penv ntm Hntm h _ _ _ _ Et). }
  assert (Hcons : (forall l j, esem l (sget lenv l (SEnt h (tl_of (rev rts)) m' r)) j
                               = if label_eqb (lden h) l then esem l (Some (ts, m)) j else esem l (sget lenv l r) j)
                  /\ (forall b, olabel_lt b (lden h) -> below b r -> below b (SEnt h (tl_of (rev rts)) m' r))
                  /\ (sorted r -> sorted (SEnt h (tl_of (rev rts)) m' r))
                  /\ (sdistd r -> tldist ts -> sdistd (SEnt h (tl_of (rev rts)) m' r))).
  { refine (conj _ (conj (fun b H1 H2 => conj H1 H2) (conj (fun H => conj Hb H) _))).
    - intros l j; cbn [sget]; destruct (label_eqb_spec (lden h) l) as [<-|]; [symmetry; apply Hsem|reflexivity].
    - intros Hr Hts; refine (conj (below_get _ _ Hb) (conj _ Hr)).
      apply (proj2 (tldist_iff lenv _)); intros t Ht; rewrite tl_list_of in Ht; apply in_rev in Ht.
      apply (proj1 (tldist_iff lenv ts) Hts); apply in_rev; exact (trim_tgts h _ _ _ _ Et t Ht). }
  destruct rts as [|x rts]; [destruct m' as [|m']|]; try exact Hcons.
  refine (conj _ (conj (fun b _ H => H) (conj (fun H => H) (fun H _ => H)))).
  intros l j; destruct (label_eqb_spec (lden h) l) as [<-|]; [|reflexivity].
  rewrite Hsem, (below_get _ _ Hb); cbn [rev tl_of]; first [apply (esem_none lenv tenv aenv penv ntm Hntm)|symmetry; apply (esem_none lenv tenv aenv penv ntm Hntm)].
Qed.

Section Merge.

Variable S0 : seg.
Hypothesis HS0 : sdistd S0.

Lemma ent_comp h ts ts' m tsS mS :
  tlen ts' = tlen ts ->
  (forall j, j < tlen ts -> rtarget_result (tden (tnth ts' j)) = cres (sden S0) (rtarget_result (tden (tnth ts j)))) ->
  ofe (sget lenv (lden h) S0) = (tsS, mS) ->
  forall j, esem (lden h) (Some (comb ts' m tsS mS)) j = cres (sden S0) (esem (lden h) (Some (ts, m)) j).
Proof.
  intros Hlen Hts0 Eo j; pose proof (sdistd_sdist lenv _ HS0) as HS'; unfold comb.
  rewrite !(esem_lsem lenv tenv aenv penv); unfold lsem; rewrite <- !tlen_list, <- !tnth_list, tlen_tcat, tlen_tskip, Hlen.
  destruct (Nat.ltb_spec j (tlen ts)) as [Hj|Hj].
  + rewrite (proj2 (Nat.ltb_lt _ _)) by lia; rewrite tnth_tcat, Hlen, (proj2 (Nat.ltb_lt _ _)) by exact Hj.
    apply Hts0, Hj.
  + cbn [cres]; rewrite (rapply_sden lenv tenv aenv penv) by exact HS'; cbn [v_label v_index].
    rewrite <- (esem_ofe lenv tenv aenv penv ntm Hntm), Eo.
    cbn [Normalise.esem]; rewrite tnth_tcat, Hlen, (proj2 (Nat.ltb_ge j (tlen ts)) Hj), tnth_tskip.
    destruct (Nat.ltb_spec (j - tlen ts + m) (tlen tsS)) as [Hk|Hk].
    * rewrite (proj2 (Nat.ltb_lt j (tlen ts + (tlen tsS - m)))) by lia; do 3 f_equal; lia.
    * rewrite (proj2 (Nat.ltb_ge j (tlen ts + (tlen tsS - m)))) by lia; do 2 f_equal.
      destruct (Nat.leb_spec (tlen tsS) m); lia.
Qed.

Lemma comb_dist ts' m tsS mS : tldist ts' -> tldist tsS -> tldist (fst (comb ts' m tsS mS)).
Proof.
  intros H1 H2; cbn [comb fst]; apply (proj2 (tldist_iff lenv _)); intros t Ht; rewrite tcat_list in Ht.
  apply in_app_or in Ht as [Ht|Ht]; [exact (proj1 (tldist_iff lenv ts') H1 t Ht)|].
  exact (proj1 (tldist_iff lenv tsS) H2 t (tskip_list_in _ _ _ Ht)).
Qed.

Definition mspec (U cur R : seg) : Prop :=
  sdistd R /\ sorted R /\ (forall b, below b U -> below b cur -> below b R)
  /\ forall l j, esem l (sget lenv l R) j
                 = match sget lenv l U with
                   | Some e => cres (sden S0) (esem l (Some e) j)
                   | None => esem l (sget lenv l cur) j
                   end.

Lemma smerge_spec U : forall cur R, sdistd U -> sorted U -> sdistd cur -> sorted cur ->
  (forall l, sget lenv l U <> None -> sget lenv l cur = sget lenv l S0) ->
  smerge F ntm S0 U cur = Some R -> mspec U cur R.
Proof.
  induction U as [|h ts m r IHU] using seg_spine; intros cur R HU HsU.
  { intros Hc HsC _ H; injection H as <-; refine (conj Hc (conj HsC (conj (fun b _ H => H) _))); intros l j; reflexivity. }
  destruct HU as [Hnr [Hts Hr]]; destruct HsU as [Hbr Hsr]; cbn [smerge].
  destruct (tlapp F ntm S0 ts) as [ts'|] eqn:Et; [|discriminate].
  destruct (proj1 (proj2 (comp_sound lenv tenv aenv penv F HF ntm Hntm S0 HS0)) ts ts' Hts Et) as [Hts' [Hlen Hts0]].
  assert (Hin : forall l, sget lenv l r <> None -> sget lenv l (SEnt h ts m r) <> None).
  { intros l H; cbn [sget]; destruct (label_eqb (lden h) l); [discriminate|exact H]. }
  assert (Hne : forall l, sget lenv l r <> None -> label_eqb (lden h) l = false).
  { intros l H; destruct (label_eqb (lden h) l) eqn:E; [|reflexivity].
    apply label_eqb_eq in E; subst l; rewrite (below_get _ _ Hbr) in H; contradiction. }
  (* putting the entry of [h], combined with the entry of [S0] *)
  assert (Hput : forall cur tsS mS cur' R0, ofe (sget lenv (lden h) S0) = (tsS, mS) -> tldist tsS ->
            below (lden h) cur' -> (forall b, below b cur -> below b cur') ->
            (forall l, label_eqb (lden h) l = false -> sget lenv l (SEnt h ts m r) = None -> sget lenv l cur' = sget lenv l cur) ->
            mspec r cur' R0 ->
            mspec (SEnt h ts m r) cur (mkent h (fst (comb ts' m tsS mS)) (snd (comb ts' m tsS mS)) R0)).
  { intros cur0 tsS mS cur' R0 Eo HtsS Hbc Hmono Hsame [Hd0 [Hs0 [Hb0 Hsem0]]].
    destruct (mkent_spec h (fst (comb ts' m tsS mS)) (snd (comb ts' m tsS mS)) R0 (Hb0 _ Hbr Hbc)) as [A [B [C D]]].
    refine (conj (D Hd0 (comb_dist _ _ _ _ Hts' HtsS)) (conj (C Hs0) (conj _ _))).
    - intros b [Hb1 Hb2] Hb3; exact (B b Hb1 (Hb0 b Hb2 (Hmono b Hb3))).
    - intros l j; rewrite A; cbn [sget]; destruct (label_eqb (lden h) l) eqn:El.
      + apply label_eqb_eq in El; subst l.
        rewrite <- surjective_pairing; exact (ent_comp h ts ts' m tsS mS Hlen Hts0 Eo j).
      + rewrite Hsem0; destruct (sget lenv l r) as [e|] eqn:Er; [reflexivity|].
        rewrite (Hsame l El); [reflexivity|]; cbn [sget]; rewrite El; exact Er. }
  revert R; induction cur as [|g tsg mg rc IHc] using seg_spine; intros R Hc HsC Hcur;
    (assert (Hh : sget lenv (lden h) S0 = sget lenv (lden h) _)
       by (symmetry; apply Hcur; cbn [sget]; rewrite label_eqb_refl; discriminate)).
  - unfold comb; destruct (smerge F ntm S0 r SNil) as [R0|] eqn:E0; [|discriminate]; intros H; injection H as <-.
    refine (Hput SNil TNil 0 SNil R0 _ I I (fun b H => H) (fun l _ _ => eq_refl) _); [rewrite Hh; reflexivity|].
    exact (IHU SNil R0 Hr Hsr I I (fun l H => Hcur l (Hin l H)) E0).
  - destruct Hc as [Hng [Htsg Hrc]]; destruct HsC as [Hbg Hsrc].
    destruct (lcmp F h g) as [[| |]|] eqn:Ec; [| | |discriminate].
    + pose proof (lcmp_sound lenv F HF _ _ _ Ec) as E; cbn in E; subst g.
      unfold comb; destruct (smerge F ntm S0 r rc) as [R0|] eqn:E0; [|discriminate]; intros H; injection H as <-.
      refine (Hput (SEnt h tsg mg rc) tsg mg rc R0 _ Htsg Hbg (fun b (H : below b (SEnt h tsg mg rc)) => proj2 H) _ _).
      * rewrite Hh; cbn [sget]; rewrite label_eqb_refl; reflexivity.
      * intros l El _; cbn [sget]; rewrite El; reflexivity.
      * refine (IHU rc R0 Hr Hsr Hrc Hsrc _ E0); intros l H.
        rewrite <- (Hcur l (Hin l H)); cbn [sget]; rewrite (Hne l H); reflexivity.
    + pose proof (lcmp_sound lenv F HF _ _ _ Ec) as Hlt; cbn in Hlt.
      assert (Hbc : below (lden h) (SEnt g tsg mg rc)) by (split; [exact Hlt|exact (below_trans _ _ _ Hlt Hbg)]).
      unfold comb; destruct (smerge F ntm S0 r (SEnt g tsg mg rc)) as [R0|] eqn:E0; [|discriminate]; intros H; injection H as <-.
      refine (Hput (SEnt g tsg mg rc) TNil 0 (SEnt g tsg mg rc) R0 _ I Hbc (fun b H => H) (fun l _ _ => eq_refl) _).
      * rewrite Hh, (below_get _ _ Hbc); reflexivity.
      * exact (IHU (SEnt g tsg mg rc) R0 Hr Hsr (conj Hng (conj Htsg Hrc)) (conj Hbg Hsrc) (fun l H => Hcur l (Hin l H)) E0).
    + pose proof (lcmp_sound lenv F HF _ _ _ Ec) as Hgt; cbn in Hgt.
      assert (HbU : below (lden g) (SEnt h ts m r)) by (split; [exact Hgt|exact (below_trans _ _ _ Hgt Hbr)]).
      assert (Hl : forall l, sget lenv l (SEnt h ts m r) <> None -> label_eqb (lden g) l = false).
      { intros l H; destruct (label_eqb (lden g) l) eqn:E; [|reflexivity].
        apply label_eqb_eq in E; subst l; rewrite (below_get _ _ HbU) in H; contradiction. }
      match goal with |- option_map _ ?x = _ -> _ => destruct x as [R1|] eqn:E1; [|discriminate] end.
      intros H; injection H as <-.
      assert (Hcur' : forall l, sget lenv l (SEnt h ts m r) <> None -> sget lenv l rc = sget lenv l S0).
      { intros l H; rewrite <- (Hcur l H); cbn [sget]; rewrite (Hl l H); reflexivity. }
      destruct (IHc R1 Hrc Hsrc Hcur' eq_refl) as [Hd1 [Hs1 [Hb1 Hsem1]]].
      pose proof (Hb1 _ HbU Hbg) as HbR.
      refine (conj (conj (below_get _ _ HbR) (conj Htsg Hd1)) (conj (conj HbR Hs1) (conj _ _))).
      * intros b HbUb [Hb2 Hb3]; exact (conj Hb2 (Hb1 b HbUb Hb3)).
      * intros l j; change (sget lenv l (SEnt g tsg mg R1)) with (if label_eqb (lden g) l then Some (tsg, mg) else sget lenv l R1).
        change (sget lenv l (SEnt g tsg mg rc)) with (if label_eqb (lden g) l then Some (tsg, mg) else sget lenv l rc).
        destruct (label_eqb (lden g) l) eqn:El; [|apply Hsem1].
        apply label_eqb_eq in El; subst l; rewrite (below_get _ _ HbU); reflexivity.
Qed.

Lemma smerge_sound U R : sdistd U -> sorted U -> sorted S0 -> smerge F ntm S0 U S0 = Some R ->
  sdistd R /\ sden R = rcompose (sden S0) (sden U).
Proof.
  intros HU HsU HsS H; destruct (smerge_spec U S0 R HU HsU HS0 HsS (fun _ _ => eq_refl) H) as [Hd [_ [_ Hsem]]].
  split; [exact Hd|]; apply rextensionality; intros [l j].
  rewrite rapply_compose_cres, !(rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; assumption).
  cbn [v_label v_index]; rewrite Hsem; destruct (sget lenv l U) as [e|]; [reflexivity|].
  cbn [Normalise.esem cres]; rewrite (rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; exact HS0); reflexivity.
Qed.

End Merge.

Lemma fcomp_sound A U R : sdistd A -> sdistd U -> fcomp F ntm A U = Some R ->
  sdistd R /\ sden R = rcompose (sden A) (sden U).
Proof.
  intros HA HU; unfold fcomp; destruct (sortb F A && sortb F U) eqn:E.
  - apply andb_true_iff in E as [E1 E2].
    exact (smerge_sound A HA U R HU (sortb_sound _ E2) (sortb_sound _ E1)).
  - exact (scomp_sound lenv tenv aenv penv F HF ntm Hntm A U R HA HU).
Qed.

(** Entries of the bound label in front of an adjustment. *)
Definition pins (ts : list (rtarget T)) (X : radj T) : radj T := fold_right (rpush_inner None) X ts.

Lemma pins_compose_l a ts X : rcompose a (pins ts X) = pins (map (rapply_target a) ts) (rcompose a X).
Proof. induction ts as [|t ts IH]; cbn [pins fold_right map]; [reflexivity|]; rewrite rcompose_push_inner_r; fold (pins ts X); rewrite IH; reflexivity. Qed.

Lemma pins_compose_r ts X B : pins ts (rcompose X B) = rcompose (pins ts X) (lifted (List.length ts) B).
Proof.
  induction ts as [|t ts IH]; cbn [pins fold_right length]; [reflexivity|].
  fold (pins ts (rcompose X B)); fold (pins ts X); rewrite IH, (rpush_inner_compose tenv ntm Hntm); reflexivity.
Qed.

Lemma tfront_sound Ts : forall s s', sdistd s -> Forall tdist Ts -> tfront F Ts s = Some s' ->
  sdistd s' /\ sden s' = pins (map tden Ts) (sden s).
Proof.
  induction Ts as [|t Ts IH]; intros s s' Hs HT; cbn [tfront fold_right].
  - intros H; injection H as <-; split; [exact Hs|reflexivity].
  - inversion HT as [|? ? Ht HT']; subst.
    fold (tfront F Ts s); destruct (tfront F Ts s) as [s0|] eqn:E; [|discriminate]; cbn [obind]; intros H.
    destruct (IH s s0 Hs HT' E) as [Hd0 D0].
    destruct (sfront_sound lenv tenv aenv penv F HF ntm Hntm LNone t s0 s' Hd0 Ht H) as [Hd D].
    split; [exact Hd|]; rewrite D, D0; reflexivity.
Qed.

Lemma thread_0 Ts K : thread F ntm 0 Ts K = None.
Proof. destruct K as [|[?|? ?] ?]; reflexivity. Qed.

Lemma thread_SS j Ts s1 K :
  thread F ntm (S (S j)) Ts (LS s1 :: K)
  = match slifts F ntm (List.length Ts) s1, thread F ntm (S j) Ts K with
    | Some a, Some b => Some (LS a :: b)
    | _, _ => None
    end.
Proof. reflexivity. Qed.

Lemma thread_nil j Ts : thread F ntm j Ts [] = None.
Proof. destruct j as [|[|j]]; reflexivity. Qed.

Lemma thread_atom j Ts L a K : thread F ntm j Ts (LA L a :: K) = None.
Proof. destruct j as [|[|j]]; reflexivity. Qed.

Lemma thread_sound j : forall Ts K Kp, lwdist K -> Forall tdist Ts -> thread F ntm j Ts K = Some Kp ->
  lwdist Kp /\ lwden Kp = pins (map (fun t => rapply_target (lwden (skipn j K)) (tden t)) Ts) (lwden K).
Proof.
  induction j as [|j IH]; intros Ts K Kp HK HT.
  { rewrite thread_0; discriminate. }
  destruct K as [|[s1|L a] K']; [rewrite thread_nil; discriminate| |rewrite thread_atom; discriminate].
  inversion HK as [|? ? Hs1 HK']; subst.
  destruct j as [|j].
  - cbn [thread]; destruct (tfront F Ts s1) as [x|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct (tfront_sound Ts s1 x Hs1 HT E) as [Hx Dx]; split; [constructor; assumption|].
    cbn [Layered.lwden skipn]; rewrite Dx, pins_compose_l, map_map; reflexivity.
  - rewrite thread_SS; destruct (slifts F ntm (List.length Ts) s1) as [a|] eqn:Ea; [|discriminate].
    destruct (thread F ntm (S j) Ts K') as [b|] eqn:Eb; [|discriminate]; intros H; injection H as <-.
    destruct (slifts_sound lenv tenv aenv penv F HF ntm Hntm _ s1 a Hs1 Ea) as [Ha Da].
    destruct (IH Ts K' b HK' HT Eb) as [Hb Db]; split; [constructor; assumption|].
    cbn [Layered.lwden]; rewrite Db, Da.
    change (skipn (S (S j)) (LS s1 :: K')) with (skipn (S j) K').
    rewrite pins_compose_r, length_map; reflexivity.
Qed.

Lemma scan_ge sig K : forall j0 j, scan F ntm sig K j0 = Some j -> j0 < j.
Proof.
  revert sig; induction K as [|[s1|L a] K IH]; intros sig j0 j; cbn [scan]; try discriminate.
  destruct (fcomp F ntm s1 sig) as [c|]; [|discriminate].
  destruct (has_terms (sdrop_none c)); [discriminate|].
  destruct (same_rest F ntm (sdrop_none c) K).
  - destruct (has_terms s1); [intros H; injection H as <-; lia|discriminate].
  - intros H; apply IH in H; lia.
Qed.

Lemma same_rest_sound sg K v : sdistd sg -> lwdist K -> same_rest F ntm sg K = true -> v_label v <> None ->
  cres (lwden K) (rapply (sden sg) v) = rapply (lwden K) v.
Proof.
  intros Hsg HK H Hv.
  assert (Hnil : sg = SNil -> cres (lwden K) (rapply (sden sg) v) = rapply (lwden K) v).
  { intros ->; change (sden SNil) with (@ridentity T); rewrite rapply_identity; reflexivity. }
  destruct sg as [|h ts m r]; [exact (Hnil eq_refl)|]; clear Hnil.
  destruct K as [|[s2|L a] K']; cbn [same_rest] in H; try discriminate.
  inversion HK as [|? ? Hs2 HK']; subst.
  destruct (fcomp F ntm s2 (SEnt h ts m r)) as [c|] eqn:Ec; [|discriminate].
  apply (proj1 (proj2 (proj2 nf_eqb_eq))) in H.
  destruct (fcomp_sound _ _ _ Hs2 Hsg Ec) as [Hc Dc].
  cbn [Layered.lwden]; rewrite (rapply_compose_cres (lwden K') (sden s2) v), <- cres_compose.
  rewrite <- (rapply_compose_cres (sden s2) (sden (SEnt h ts m r)) v), <- Dc.
  rewrite (named_sdrop_none lenv tenv aenv penv c v Hv), H, <- (named_sdrop_none lenv tenv aenv penv s2 v Hv).
  reflexivity.
Qed.

Lemma scan_sound K : forall sig j0 j v, sdistd sig -> lwdist K -> scan F ntm sig K j0 = Some j -> v_label v <> None ->
  cres (lwden K) (rapply (sden sig) v) = rapply (lwden (skipn (j - j0) K)) v.
Proof.
  induction K as [|[s1|L a] K IH]; intros sig j0 j v Hsig HK; cbn [scan]; try discriminate.
  inversion HK as [|? ? Hs1 HK']; subst.
  destruct (fcomp F ntm s1 sig) as [c|] eqn:Ec; [|discriminate].
  destruct (fcomp_sound _ _ _ Hs1 Hsig Ec) as [Hc Dc].
  pose proof (sdrop_dd lenv _ Hc) as Hsg.
  destruct (has_terms (sdrop_none c)); [discriminate|].
  assert (E0 : forall v, v_label v <> None ->
            cres (lwden (LS s1 :: K)) (rapply (sden sig) v) = cres (lwden K) (rapply (sden (sdrop_none c)) v)).
  { intros w Hw; cbn [Layered.lwden]; rewrite <- cres_compose, <- (rapply_compose_cres (sden s1) (sden sig) w), <- Dc.
    rewrite (named_sdrop_none lenv tenv aenv penv c w Hw); reflexivity. }
  destruct (same_rest F ntm (sdrop_none c) K) eqn:Es.
  - destruct (has_terms s1); [|discriminate]; intros H Hv; injection H as <-.
    replace (S j0 - j0) with 1 by lia; cbn [skipn]; rewrite (E0 v Hv).
    exact (same_rest_sound _ K v Hsg HK' Es Hv).
  - intros H Hv; pose proof (scan_ge _ _ _ _ H) as Hj.
    rewrite (E0 v Hv), (IH _ _ _ v Hsg HK' H Hv).
    replace (j - j0) with (S (j - S j0)) by lia; reflexivity.
Qed.

Lemma pure_target (A B : radj T) t : is_pure ntm t = true ->
  (forall v, v_label v <> None -> rapply A v = rapply B v) ->
  tdist t /\ rapply_target A (tden t) = rapply_target B (tden t).
Proof.
  destruct t as [|u [[|]|] [|]]; try discriminate; cbn [is_pure]; intros Hu Hn; apply Nat.ltb_lt in Hu.
  split; [exact I|].
  destruct (nth_error tenv u) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
  rewrite (tden_bind lenv tenv aenv penv u (WEnd SNil) None y Ey); cbn [rapply_target bden].
  rewrite (wden_id lenv tenv aenv penv), rpcompose_identity; f_equal; apply rpcompose_named, Hn.
Qed.

Lemma unterm_sound s sa Ts : sdistd s -> unterm F ntm s = Some (sa, Ts) ->
  sdistd sa /\ forallb (is_pure ntm) Ts = true /\ sden s = rcompose (pins (map tden Ts) ridentity) (sden sa).
Proof.
  intros Hs; unfold unterm.
  destruct (fcomp F ntm (shseg LNone (nterms s)) s) as [s1|]; [|discriminate].
  destruct (rents (ents s1) 0) as [es T0].
  destruct (mkseg F es) as [sa0|]; [|discriminate].
  destruct (tfront F T0 SNil) as [eT|] eqn:Et; [|discriminate].
  destruct (fcomp F ntm eT sa0) as [s2|] eqn:Ec; [|discriminate].
  destruct (seg_eqb s2 s && forallb (is_pure ntm) T0 && sdistb F sa0) eqn:Eb; [|discriminate].
  intros H; injection H as <- <-.
  apply andb_true_iff in Eb as [Eb H3]; apply andb_true_iff in Eb as [H1 H2].
  apply (proj1 (proj2 (proj2 nf_eqb_eq))) in H1; subst s2.
  pose proof (sdistb_sound _ H3) as Hsa.
  assert (HT : Forall tdist T0).
  { apply Forall_forall; intros t Ht; rewrite forallb_forall in H2.
    exact (proj1 (pure_target ridentity ridentity t (H2 t Ht) (fun _ _ => eq_refl))). }
  destruct (tfront_sound T0 SNil eT I HT Et) as [He De].
  destruct (fcomp_sound _ _ _ He Hsa Ec) as [_ Dc].
  refine (conj Hsa (conj H2 _)); rewrite Dc, De; reflexivity.
Qed.

Lemma try_join_sound s s1 K0 j sa Kp : sdistd s -> lwdist (LS s1 :: K0) ->
  try_join F ntm s s1 (LS s1 :: K0) = Some (j, sa, Kp) ->
  sdistd sa /\ lwdist Kp /\ rcompose (lwden Kp) (sden sa) = rcompose (lwden (LS s1 :: K0)) (sden s).
Proof.
  intros Hs HK; unfold try_join; set (K := LS s1 :: K0) in *.
  destruct (named_term s1); [discriminate|].
  destruct (scan F ntm SNil K 0) as [j'|] eqn:Esc; [|discriminate].
  destruct (unterm F ntm s) as [[sa' Ts]|] eqn:Eu; [|discriminate]; cbn [obind].
  destruct (thread F ntm j' Ts K) as [Kp'|] eqn:Et; [|discriminate]; cbn [obind]; intros H; injection H as <- <- <-.
  destruct (unterm_sound s sa' Ts Hs Eu) as [Hsa [Hp Ds]].
  assert (Hn : forall v, v_label v <> None -> rapply (lwden K) v = rapply (lwden (skipn j' K)) v).
  { intros v Hv; pose proof (scan_sound K SNil 0 j' v I HK Esc Hv) as E.
    change (sden SNil) with (@ridentity T) in E; rewrite rapply_identity, Nat.sub_0_r in E; exact E. }
  assert (HT : Forall tdist Ts).
  { apply Forall_forall; intros t Ht; rewrite forallb_forall in Hp; exact (proj1 (pure_target _ _ t (Hp t Ht) Hn)). }
  destruct (thread_sound j' Ts K Kp' HK HT Et) as [HKp DKp].
  refine (conj Hsa (conj HKp _)).
  assert (Em : map (fun t => rapply_target (lwden (skipn j' K)) (tden t)) Ts
               = map (fun t => rapply_target (lwden K) (tden t)) Ts).
  { apply map_ext_in; intros t Ht; rewrite forallb_forall in Hp; symmetry; exact (proj2 (pure_target _ _ t (Hp t Ht) Hn)). }
  rewrite DKp, Em, Ds, (rcompose_assoc (lwden K)), pins_compose_l, rcompose_identity_r, map_map; reflexivity.
Qed.

Lemma swap_sound s s1 sa f1 n rho : sdistd s -> sdistd s1 -> swap F ntm s s1 = Some (sa, f1, n, rho) ->
  sdistd sa /\ sdistd f1 /\ sdistd n /\ sdistd rho
  /\ rcompose (sden rho) (rcompose (sden n) (rcompose (sden f1) (sden sa))) = rcompose (sden s1) (sden s).
Proof.
  intros Hs Hs1; unfold swap.
  destruct (sinv F (sdrop_none s1)) as [[nu R]|]; [|discriminate].
  destruct (unterm F ntm s) as [[sa' Ts]|] eqn:Eu; [|discriminate].
  destruct (slifts F ntm (List.length Ts) s1) as [f1'|] eqn:Ef; [|discriminate].
  destruct (obind (sset F LNone TNil (List.length R) nu) (tfront F Ts)) as [n'|]; [|discriminate].
  destruct (sset F LNone (tl_of R) 0 (sdrop_none s1)) as [rho'|]; [|discriminate].
  destruct (fcomp F ntm s1 s) as [c1|] eqn:E1; [|discriminate].
  destruct (fcomp F ntm f1' sa') as [t1|] eqn:Et1; [|discriminate]; cbn [obind].
  destruct (fcomp F ntm n' t1) as [t2|] eqn:Et2; [|discriminate]; cbn [obind].
  destruct (fcomp F ntm rho' t2) as [c2|] eqn:Et3; [|discriminate].
  destruct (seg_eqb c1 c2 && sdistb F n' && sdistb F rho') eqn:Eb; [|discriminate].
  intros H; injection H as <- <- <- <-.
  apply andb_true_iff in Eb as [Eb H3]; apply andb_true_iff in Eb as [H1 H2].
  apply (proj1 (proj2 (proj2 nf_eqb_eq))) in H1; subst c2.
  pose proof (sdistb_sound _ H2) as Hn; pose proof (sdistb_sound _ H3) as Hr.
  destruct (unterm_sound s sa' Ts Hs Eu) as [Hsa _].
  destruct (slifts_sound lenv tenv aenv penv F HF ntm Hntm _ s1 f1' Hs1 Ef) as [Hf _].
  destruct (fcomp_sound _ _ _ Hs1 Hs E1) as [_ D1].
  destruct (fcomp_sound _ _ _ Hf Hsa Et1) as [Ht1 Dt1].
  destruct (fcomp_sound _ _ _ Hn Ht1 Et2) as [Ht2 Dt2].
  destruct (fcomp_sound _ _ _ Hr Ht2 Et3) as [_ Dt3].
  refine (conj Hsa (conj Hf (conj Hn (conj Hr _)))); rewrite <- D1, Dt3, Dt2, Dt1; reflexivity.
Qed.

Lemma iface_c_sound s s1 s' s1' : sdistd s -> sdistd s1 -> iface_c F ntm s s1 = (s', s1') ->
  sdistd s' /\ sdistd s1' /\ rcompose (sden s1') (sden s') = rcompose (sden s1) (sden s).
Proof.
  intros Hs Hs1; unfold iface_c.
  assert (Hid : (s, s1) = (s', s1') -> sdistd s' /\ sdistd s1' /\ rcompose (sden s1') (sden s') = rcompose (sden s1) (sden s))
    by (intros H; injection H as <- <-; auto).
  destruct (iface F ntm nolim s s1) as [[a b]|]; [|exact Hid].
  destruct (pair_ok F ntm s s1 a b && sdistb F a && sdistb F b) eqn:Eb; [|exact Hid].
  intros H; injection H as <- <-.
  apply andb_true_iff in Eb as [Eb H3]; apply andb_true_iff in Eb as [H1 H2].
  pose proof (sdistb_sound _ H2) as Ha; pose proof (sdistb_sound _ H3) as Hb.
  unfold pair_ok in H1.
  destruct (fcomp F ntm s1 s) as [c1|] eqn:E1; [|discriminate].
  destruct (fcomp F ntm b a) as [c2|] eqn:E2; [|discriminate].
  apply (proj1 (proj2 (proj2 nf_eqb_eq))) in H1; subst c2.
  destruct (fcomp_sound _ _ _ Hs1 Hs E1) as [_ D1].
  destruct (fcomp_sound _ _ _ Hb Ha E2) as [_ D2].
  refine (conj Ha (conj Hb _)); rewrite <- D1, <- D2; reflexivity.
Qed.

Definition cc_ok (cc : seg -> lword -> option lword) : Prop :=
  forall s K K', sdistd s -> lwdist K -> cc s K = Some K' -> lwdist K' /\ lwden K' = rcompose (lwden K) (sden s).

Lemma reroute_c_sound s s1 : sdistd s -> sdistd s1 ->
  sdistd (reroute_c F ntm s s1) /\ rcompose (sden s1) (sden (reroute_c F ntm s s1)) = rcompose (sden s1) (sden s).
Proof.
  intros Hs Hs1; unfold reroute_c.
  destruct (reroute F ntm nolim s s1) as [a|]; [|auto].
  destruct (pair_ok F ntm s s1 a s1 && sdistb F a) eqn:Eb; [|auto].
  apply andb_true_iff in Eb as [H1 H2]; pose proof (sdistb_sound _ H2) as Ha.
  unfold pair_ok in H1.
  destruct (fcomp F ntm s1 s) as [c1|] eqn:E1; [|discriminate].
  destruct (fcomp F ntm s1 a) as [c2|] eqn:E2; [|discriminate].
  apply (proj1 (proj2 (proj2 nf_eqb_eq))) in H1; subst c2.
  destruct (fcomp_sound _ _ _ Hs1 Hs E1) as [_ D1].
  destruct (fcomp_sound _ _ _ Hs1 Ha E2) as [_ D2].
  split; [exact Ha|]; rewrite <- D1, <- D2; reflexivity.
Qed.

Lemma rr_up_sound n : forall l, lwdist l -> lwdist (rr_up F ntm n l) /\ lwden (rr_up F ntm n l) = lwden l.
Proof.
  induction n as [|n IH]; intros l Hl; [destruct l as [|[?|? ?] ?]; auto|].
  destruct l as [|[x|L a] r]; [auto| |auto].
  inversion Hl as [|? ? Hx Hr]; subst; cbn [rr_up].
  destruct (IH r Hr) as [H1 D1].
  destruct (rr_up F ntm n r) as [|[y|L a] r0] eqn:E.
  - split; [constructor; assumption|]; cbn [Layered.lwden] in *; rewrite D1; reflexivity.
  - inversion H1 as [|? ? Hy Hr0]; subst.
    destruct (reroute_c_sound x y Hx Hy) as [Hx' Dx].
    split; [constructor; [exact Hx'|exact H1]|].
    cbn [Layered.lwden] in *; rewrite <- D1, <- !rcompose_assoc, Dx; reflexivity.
  - split; [constructor; assumption|]; cbn [Layered.lwden] in *; rewrite D1; reflexivity.
Qed.

Lemma sweep_sound cc (Hcc : cc_ok cc) n : forall s K K', sdistd s -> lwdist K -> sweep F ntm cc n s K = Some K' ->
  lwdist K' /\ lwden K' = rcompose (lwden K) (sden s).
Proof.
  induction n as [|n IH]; intros s K K' Hs HK; [destruct K as [|[?|? ?] ?]; exact (Hcc s _ K' Hs HK)|].
  destruct K as [|[s1|L a] K0]; [exact (Hcc s _ K' Hs HK)| |exact (Hcc s _ K' Hs HK)].
  inversion HK as [|? ? Hs1 HK0]; subst; cbn [sweep].
  destruct (iface_c F ntm s s1) as [s' s1'] eqn:Ei.
  destruct (iface_c_sound s s1 s' s1' Hs Hs1 Ei) as [Hs' [Hs1' D]].
  assert (Hgen : forall X, lwdist X -> lwden X = rcompose (lwden K0) (sden s1') ->
            forall Y, lwdist Y /\ lwden Y = rcompose (lwden X) (sden s') ->
            lwdist Y /\ lwden Y = rcompose (lwden (LS s1 :: K0)) (sden s)).
  { intros X HX DX Y [A B]; split; [exact A|]; rewrite B, DX; cbn [Layered.lwden]; rewrite <- !rcompose_assoc, D; reflexivity. }
  destruct s1' as [|h ts m r].
  { intros H; refine (Hgen K0 HK0 _ K' (Hcc s' K0 K' Hs' HK0 H)).
    change (sden SNil) with (@ridentity T); rewrite rcompose_identity_r; reflexivity. }
  destruct (has_terms (SEnt h ts m r)).
  - destruct (sweep F ntm cc n (SEnt h ts m r) K0) as [K1|] eqn:E1; [|discriminate]; cbn [option_map]; intros H; injection H as <-.
    destruct (IH _ K0 K1 Hs1' HK0 E1) as [H1 D1].
    apply (Hgen K1 H1 D1); split; [constructor; assumption|reflexivity].
  - destruct (cc (SEnt h ts m r) K0) as [K1|] eqn:E1; [|discriminate]; cbn [obind]; intros H.
    destruct (Hcc _ K0 K1 Hs1' HK0 E1) as [H1 D1].
    exact (Hgen K1 H1 D1 K' (Hcc s' K1 K' Hs' H1 H)).
Qed.

Lemma ccons_sound fuel : cc_ok (ccons F ntm fuel).
Proof.
  induction fuel as [|f IH]; intros s K K' Hs HK;
    [exact (cons_seg_sound lenv tenv aenv penv F HF ntm Hntm K s K' Hs HK)|].
  destruct K as [|[s1|L a] K0];
    [exact (cons_seg_sound lenv tenv aenv penv F HF ntm Hntm _ s K' Hs HK)|
    |exact (cons_seg_sound lenv tenv aenv penv F HF ntm Hntm _ s K' Hs HK)].
  inversion HK as [|? ? Hs1 HK0]; subst; cbn [ccons].
  destruct (negb (has_terms s) || (bound_only s1 && no_atoms s)).
  { destruct (fcomp F ntm s1 s) as [s'|] eqn:E; [|discriminate].
    destruct (fcomp_sound _ _ _ Hs1 Hs E) as [Hd D].
    assert (Hgen : lwdist K' /\ lwden K' = rcompose (lwden K0) (sden s') ->
                   lwdist K' /\ lwden K' = rcompose (lwden (LS s1 :: K0)) (sden s)).
    { intros [A B]; split; [exact A|]; rewrite B, D; cbn [Layered.lwden]; rewrite rcompose_assoc; reflexivity. }
    destruct s' as [|h ts m r]; [|exact (fun H => Hgen (IH _ K0 K' Hd HK0 H))].
    intros H; injection H as <-; apply Hgen; split; [exact HK0|].
    change (sden SNil) with (@ridentity T); rewrite rcompose_identity_r; reflexivity. }
  destruct (try_join F ntm s s1 (LS s1 :: K0)) as [[[j sa] Kp]|] eqn:Ej.
  { destruct (try_join_sound s s1 K0 j sa Kp Hs HK Ej) as [Hsa [HKp D]].
    destruct Kp as [|[p1|? ?] Kp']; try discriminate.
    inversion HKp as [|? ? Hp1 HKp']; subst.
    destruct (fcomp F ntm p1 sa) as [sm|] eqn:Em; [|discriminate]; intros H.
    destruct (fcomp_sound _ _ _ Hp1 Hsa Em) as [Hsm Dm].
    assert (Hl : lwdist (LS sm :: Kp')) by (constructor; assumption).
    destruct (rr_up_sound j _ Hl) as [Hu Du].
    destruct (rr_up F ntm j (LS sm :: Kp')) as [|[x|? ?] r]; try discriminate.
    inversion Hu as [|? ? Hx Hr]; subst.
    destruct (sweep_sound _ IH j x r K' Hx Hr H) as [A B]; split; [exact A|].
    cbn [Layered.lwden] in Du; rewrite B, Du, Dm, rcompose_assoc; exact D. }
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
  destruct (iface_c F ntm s s1) as [s' s1'] eqn:Ei.
  destruct (iface_c_sound s s1 s' s1' Hs Hs1 Ei) as [Hs' [Hs1' D]].
  assert (Hgen : forall X, lwdist X -> lwden X = rcompose (lwden K0) (sden s1') ->
            forall Y, lwdist Y /\ lwden Y = rcompose (lwden X) (sden s') ->
            lwdist Y /\ lwden Y = rcompose (lwden (LS s1 :: K0)) (sden s)).
  { intros X HX DX Y [A B]; split; [exact A|]; rewrite B, DX; cbn [Layered.lwden]; rewrite <- !rcompose_assoc, D; reflexivity. }
  destruct (seg_eqb s1 s1') eqn:Eq.
  { apply (proj1 (proj2 (proj2 nf_eqb_eq))) in Eq; subst s1'; intros H; injection H as <-.
    apply (Hgen (LS s1 :: K0) HK eq_refl); split; [constructor; [exact Hs'|exact HK]|reflexivity]. }
  destruct s1' as [|h ts m r].
  { intros H; refine (Hgen K0 HK0 _ K' (IH s' K0 K' Hs' HK0 H)).
    change (sden SNil) with (@ridentity T); rewrite rcompose_identity_r; reflexivity. }
  destruct (ccons F ntm f (SEnt h ts m r) K0) as [K1|] eqn:E1; [|discriminate]; cbn [obind]; intros H.
  destruct (IH _ K0 K1 Hs1' HK0 E1) as [H1 D1].
  exact (Hgen K1 H1 D1 K' (IH s' K1 K' Hs' H1 H)).
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
    destruct (canon_f F ntm fuel r) as [r'|] eqn:E; [|discriminate]; cbn [option_map]; intros H; injection H as <-.
    destruct (IH r' Hr eq_refl) as [H1 D1]; split; [constructor; [exact I|exact H1]|].
    cbn [Layered.lwden]; rewrite D1; reflexivity.
Qed.

Theorem canon_sound l l' : lwdist l -> canon F ntm l = Some l' -> lwdist l' /\ lwden l' = lwden l.
Proof. apply canon_f_sound. Qed.

End Sound.
