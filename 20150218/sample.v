(* sample.v 2015/02/08 Y.Mizoguchi *)

Require Import Ssreflect.ssreflect Ssreflect.ssrbool.
Require Import Ssreflect.ssrfun Ssreflect.ssrnat Ssreflect.seq.
Require Import MathComp.div.

Section Sigma.
Lemma lemma0: forall n:nat, n + 0 = n.
Proof.
  elim.                         (* nに対する数学的帰納法で証明 *)
  rewrite /addn/addn_rec/plus.
  apply (erefl 0).              (* n=0のときは明らか *)
  move => n H.
  rewrite /addn/addn_rec/plus.
  fold plus.
  rewrite plusE.
  rewrite H.                    (* nのときの仮定を使って *)
  apply (erefl (n.+1)).         (* n+1のときの証明が出来る *)
Qed.

Print lemma0.

Lemma lemma1: forall n:nat,
  (n.+1)*2 + (n * (n.+1)) = (n.+1 * (n.+2)).
Proof.
  move => n.
  ring.
Qed.

Lemma lemma2: forall n:nat,
  (n.+1 * 2) %/ 2 = n.+1.
Proof.
  move => n.
  rewrite -(muln_divA (n.+1)).
  rewrite (divnn 2).
  simpl.
  rewrite muln1.
  apply (erefl (n.+1)).
  apply (dvdnn 2).
Qed.

Lemma lemma3: forall n:nat,
  2 %| (n.+1 * 2).
Proof.
  move => n.
  apply dvdn_mull.
  apply (dvdnn 2).
Qed.

Lemma lemma4: forall n:nat,
  n.+1 + (n * n.+1) %/ 2 = (n.+1 * n.+2) %/ 2.
Proof.
  move => n.
  rewrite -lemma1.
  rewrite (divnDl (n*n.+1) (lemma3 n)).
  rewrite lemma2.
  apply erefl.
Qed.

Fixpoint f (n:nat) :=
match n with
| 0 => 0
| p.+1 => (p.+1) + (f p)
end.

Definition g (n:nat) := ((n * (n.+1)) %/ 2).

Theorem sigma: forall n:nat, (f n) = (g n).
Proof.
  elim.              (* nに対する数学的帰納法で証明 *)
  by [compute].      (* n=0のときは計算で明らか *)
  move => n H.
  rewrite /f.
  fold f.
  rewrite H.         (* nのときの仮定を使うと *)
  rewrite /g.
  apply lemma4.      (* lemma4の計算から証明できる *)
Qed.
End Sigma.

Extraction Language Haskell.

Extract Inductive list => "([])" ["[]" "(:)"].
Extract Inductive sumbool => "Prelude.Bool"
             ["Prelude.True" "Prelude.False"].
Extract Inductive bool => "Prelude.Bool"
             ["Prelude.True" "Prelude.False"].
Extract Inductive nat => "Prelude.Int"
             ["0" "Prelude.succ"]
             "(\fO fS n -> if (n Prelude.== 0)
               then fO () else fS (n Prelude.- 1))".

Extraction "sigma.hs" f g.

Section Negative.

Definition E1 (x:nat):Prop :=
match x with
| 0    => False
| n.+1 => match n with
          | 0    => True
          | _.+1 => False
          end
end.

Compute [:: (E1 0); (E1 1); (E1 2); (E1 3)].

Lemma lemma5: (E1 0) -> False.
Proof.
compute.
apply (False_rect False).
Qed.

Print False_rect.

Check eq_ind.
Check I.
Check (@eq_ind nat 1 E1 I 0).

Lemma lemma6: (1 = 0) -> False.
Proof.
have: (E1 1).
compute.
apply I.
move => H1 H2; move: H1.
rewrite H2.
apply lemma5.
(* apply (@eq_ind nat 1 E1 I 0). *)
Qed.

End Negative.

Print False_rect.

Section Even.

Definition NE1 (x:nat):Prop :=
match x with
| 0    => True
| n.+1 => match n with
          | 0    => False
          | _.+1 => True
          end
end.

Inductive even: nat -> Prop :=
|even_0:  even 0
|even_SS: forall n, (even n) -> (even (n.+2)).

Lemma lemma7: (even 2).
Proof.
apply (even_SS 0 even_0).
Qed.

Lemma lemma8: forall n, (even n) -> (NE1 n).
Proof.
  move => n.
  case.         (* evenの構成の帰納法で証明 *)
  compute.      (* (even 0)のときは計算で明らか *)
  apply I.
  move => n0 H.
  compute.      (* (even (n.+2))のときも計算で明らか *)
  apply I.
Qed.

Lemma lemma9: (even 1) -> False.
Proof.
apply (lemma8 1).
Qed.

Print lemma8.
Print lemma9.

Lemma lemma10: (even 1) -> False.
Proof.
move => H.
inversion H.
Qed.

Print lemma10.


Lemma lemma11: forall n, ~ (E1 n) <-> (NE1 n).
Proof.
move => n.
split.
case n.
move => H.
compute.
apply I.
case.
compute.
move => H.
apply (H I).
move => n0.
move => H.
compute.
apply I.
case n.
move => H.
compute.
apply (False_rect False).
case.
compute.
move => H1 H2.
apply H1.
move => n0.
compute.
move => H1 H2.
apply H2.
Qed.

End Even.
