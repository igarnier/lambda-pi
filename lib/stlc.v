Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Logic.Decidable.
Require Import Stdlib.Lists.List.

Inductive typ : Type :=
| TInt : typ
| TArrow : typ -> typ -> typ
| TProd : typ -> typ -> typ.

Inductive name : Type :=
| Global : string -> name
| Local : Z -> name
| Quote : Z -> name.

Inductive inferrable : Type :=
| Annot : checkable -> typ -> inferrable
| Bound : nat -> inferrable
| Meta : nat -> inferrable
| Free : name -> inferrable
| LetMeta : typ -> checkable -> inferrable
| App : inferrable -> checkable -> inferrable
| Int : Z -> inferrable

with checkable : Type :=
| Inf : inferrable -> checkable
| Lam : checkable -> checkable
| Pair : checkable -> checkable -> checkable.

Definition env (A : Type) := list A.

Inductive value : Type :=
| VNeutral : neutral -> value
| VInt : Z -> value
| VLam : env value * checkable -> value
| VPair : value * value -> value

with neutral : Type :=
| NFree : name -> neutral
| NApp : neutral -> value -> neutral.

Inductive meta_state : Type :=
| Undef : checkable -> meta_state
| Sketched : value -> meta_state.

Lemma typ_eq_def : forall t1 t2:typ, {t1 = t2} + {t1 <> t2}.
Proof.
intros.
decide equality.
Qed.

Lemma name_eq_def : forall n1 n2:name, {n1 = n2} + {n1 <> n2}.
Proof.
intros.
elim n1.
{
  elim n2.
  { intros s1 s2.
    elim (string_dec s1 s2).
    { intro Heq.
      rewrite Heq.
      left.
      reflexivity. }
    { intro Hneq.
      right.
      congruence. } }
  { intros i1 i2.
    right.
    discriminate. }
  { intros z s.
    right.
    discriminate. } }
{
  elim n2.
  { intros s z.
    right.
    discriminate. }
  { intros z1 z2.
    elim (Z.eq_dec z1 z2).
    { intro Heq.
      rewrite Heq.
      left.
      reflexivity. }
    { intro Hneq.
      right.
      congruence. } }
  { intros z1 z2.
    right.
    discriminate. } }
{
  elim n2.
  { intros s z.
    right.
    discriminate. }
  { intros z1 z2.
    right.
    discriminate. }
  { intros z1 z2.
    elim (Z.eq_dec z1 z2).
    { intro Heq.
      rewrite Heq.
     left.
     reflexivity. }
   { intro Hneq.
     right.
     congruence. } } }
Qed.

Fixpoint subst_checkable (i : nat) (name : inferrable) (ct : checkable) : checkable :=
  match ct with
  | Inf inf => Inf (subst_inferrable i name inf)
  | Lam ct' => Lam (subst_checkable i name ct')
  | Pair ct1 ct2 => Pair (subst_checkable i name ct1) (subst_checkable i name ct2)
  end

with subst_inferrable (i : nat) (name : inferrable) (it : inferrable) : inferrable :=
  match it with
  | Annot ct t => Annot (subst_checkable i name ct) t
  | Bound j => if Nat.eq_dec i j then name else it
  | Meta _ => it
  | Free _ => it
  | LetMeta typ ct => LetMeta typ (subst_checkable i name ct)
  | App inf ct => App (subst_inferrable i name inf) (subst_checkable i name ct)
  | Int _ => it
  end.

Definition eval_env := env value.
Definition sketch_env := env meta_state.

Fixpoint eval_checkable (fuel : nat) (env : eval_env) (senv : sketch_env) (ct : checkable) { struct fuel } : option value :=
  match fuel with
  | 0 => None
  | S fuel =>
      match ct with
      | Inf inf => eval_inferrable fuel env senv inf
      | Lam ct' => Some (VLam (env, ct'))
      | Pair ct1 ct2 =>
          match eval_checkable fuel env senv ct1, eval_checkable fuel env senv ct2 with
          | Some v1, Some v2 => Some (VPair (v1, v2))
          | _, _ => None
          end
      end
  end

with eval_inferrable (fuel : nat) (env : eval_env) (senv : sketch_env) (it : inferrable) { struct fuel } : option value :=
       match fuel with
       | 0 => None
       | S fuel =>
           match it with
           | Annot ct t => eval_checkable fuel env senv ct
           | Bound j => nth_error env j
           | Meta j =>
               match nth_error senv j with
               | None => None
               | Some (Undef _) => None
               | Some (Sketched v) => Some v
               end
           | Free n => Some (VNeutral (NFree n))
           | LetMeta typ ct =>
               match eval_checkable fuel env senv ct with
               | None => None
               | Some v => Some v
               end
           | App inf ct =>
               match eval_inferrable fuel env senv inf with
               | None => None
               | Some (VNeutral n) =>
                   match eval_checkable fuel env senv ct with
                   | None => None
                   | Some v => Some (VNeutral (NApp n v))
                   end
               | Some (VLam (env, body)) =>
                   match  eval_checkable fuel env senv ct with
                   | None => None
                   | Some v => eval_checkable fuel (v :: env) senv body
                   end
               | Some (VInt _) => None
               | Some (VPair _) => None
               end
           | Int z => Some (VInt z)
           end
       end.
