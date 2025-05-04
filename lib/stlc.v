Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Logic.Decidable.
Require Import Stdlib.Lists.List.

Inductive typ : Type :=
| TInt : typ
| TArrow : typ -> typ -> typ.

Inductive name : Type :=
| Global : string -> name
| Local : Z -> name
| Quote : Z -> name.

Inductive inferrable : Type :=
| Annot : checkable -> typ -> inferrable
| Bound : nat -> inferrable
| Free : name -> inferrable
| App : inferrable -> checkable -> inferrable
| Int : Z -> inferrable

with checkable : Type :=
| Inf : inferrable -> checkable
| Lam : checkable -> checkable.

Definition env (A : Type) := list A.

Inductive value : Type :=
| VNeutral : neutral -> value
| VInt : Z -> value
| VLam : env value * checkable -> value

with neutral : Type :=
| NFree : name -> neutral
| NApp : neutral -> value -> neutral.

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
  end

with subst_inferrable (i : nat) (name : inferrable) (it : inferrable) : inferrable :=
  match it with
  | Annot ct t => Annot (subst_checkable i name ct) t
  | Bound j => if Nat.eq_dec i j then name else it
  | Free n => it
  | App inf ct => App (subst_inferrable i name inf) (subst_checkable i name ct)
  | Int z => it
  end.

Fixpoint eval_checkable (fuel : nat) (env : env value) (ct : checkable) { struct fuel } : option value :=
  match fuel with
  | 0 => None
  | S fuel =>
      match ct with
      | Inf inf => eval_inferrable fuel env inf
      | Lam ct' => Some (VLam (env, ct'))
      end
  end

with eval_inferrable (fuel : nat) (env : env value) (it : inferrable) { struct fuel } : option value :=
       match fuel with
       | 0 => None
       | S fuel =>
           match it with
           | Annot ct t => eval_checkable fuel env ct
           | Bound j => nth_error env j
           | Free n => Some (VNeutral (NFree n))
           | App inf ct => match eval_inferrable fuel env inf with
                           | None => None
                           | Some (VNeutral n) =>
                               match eval_checkable fuel env ct with
                               | None => None
                               | Some v => Some (VNeutral (NApp n v))
                               end
                           | Some (VLam (env, body)) =>
                               match  eval_checkable fuel env ct with
                               | None => None
                               | Some v =>
                                   eval_checkable fuel (v :: env) body
                               end
                           | Some (VInt _) => None
                           end
           | Int z => Some (VInt z)
           end
       end.
