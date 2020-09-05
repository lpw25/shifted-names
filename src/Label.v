Require Import Ascii String StrictProp.

Definition label := string.

Definition label_dec s1 s2 := string_dec s1 s2.
Arguments label_dec !s1 !s2.

Definition is_less_than_ascii (a1 : ascii) (a2 : ascii) :=
  match a1, a2 with
  | Ascii b11 b12 b13 b14 b15 b16 b17 b18,
    Ascii b21 b22 b23 b24 b25 b26 b27 b28 =>
    match b18, b28 with
    | true, false => false
    | false, true => true
    | _, _ =>
      match b17, b27 with
      | true, false => false
      | false, true => true
      | _, _ =>
        match b16, b26 with
        | true, false => false
        | false, true => true
        | _, _ =>
          match b15, b25 with
          | true, false => false
          | false, true => true
          | _, _ =>
            match b14, b24 with
            | true, false => false
            | false, true => true
            | _, _ =>
              match b13, b23 with
              | true, false => false
              | false, true => true
              | _, _ =>
                match b12, b22 with
                | true, false => false
                | false, true => true
                | _, _ =>
                  match b11, b21 with
                  | true, false => false
                  | false, true => true
                  | _, _ => false
                  end
                end
              end
            end
          end
        end
      end
    end
  end.

Fixpoint is_less_than_label s1 s2 :=
  match s1, s2 with
  | EmptyString, EmptyString => false
  | String a1 s1, EmptyString => false
  | EmptyString, String a2 s2 => true
  | String a1 s1, String a2 s2 =>
    if is_less_than_ascii a1 a2 then true
    else if is_less_than_ascii a2 a1 then false
    else is_less_than_label s1 s2
  end.

Definition less_than_label s1 s2 :=
  if is_less_than_label s1 s2 then sUnit else sEmpty.

Definition label_opt_dec (s1 s2 : option label)
  : {s1 = s2} + {s1 <> s2}.
  decide equality.
  apply label_dec.
Defined.

Definition label_opt_eqb s1 s2 : bool :=
  match label_opt_dec s1 s2 with
  | left _ => true
  | right _ => false
  end.
