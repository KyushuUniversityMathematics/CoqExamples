(* Tppmark2014.v 2015/05/15 Y.Mizoguchi *)
(* Original tppmark_hirai_ym.v 2015/05/15 *)

(** %
\section{第4回「TPPmark2014を解く」}

今回は, TPP2014\footnote{\url{http://imi.kyushu-u.ac.jp/lasm/tpp2014/}}で出題された以下の問題を解く.

\begin{screen}
\noindent
Let $\mathbf{N}=\{0,1,2,3,\cdots\}$ be a set of natural numbers,
$p \in \mathbf{N}$ and $q \in \mathbf{N}$.
We denote $(p \, \mathbf{mod} \, q) = r$
if and only if 
there exist $k \in \mathbf{N}$ and $r \in \mathbf{N}$ such that
$p = k q + r$ and $0 \leqq r < q$.
Further, we denote $(q\,\vert\,p)$
if and only if $(p \, \mathbf{mod} \, q) = 0$.
Prove the following questions:
\begin{enumerate}
\item[(i)] For any $a \in \mathbf{N}$,
$(a^2 \, \mathbf{mod}\, 3)=0$ or $(a^2 \, \mathbf{mod}\, 3)=1$.
\item[(ii)] Let $a \in \mathbf{N}$, $b \in \mathbf{N}$ and $c \in \mathbf{N}$.
If $a^2 + b^2 = 3 c^2$ then
$(3\,\vert\,a)$, $(3\,\vert\,b)$ and $(3\,\vert\,c)$.
\item[(iii)] Let $a \in \mathbf{N}$, $b \in \mathbf{N}$ and $c \in \mathbf{N}$.
If $a^2 + b^2 = 3c^2$ then $a=b=c=0$.
\end{enumerate}
\end{screen}

% **)

Require Import Ssreflect.ssreflect Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat MathComp.div MathComp.prime.

(** %
\section{補題}
% **)

Lemma three n P : P 0 -> P 1 -> P 2 -> P (n %% 3).
Proof.
move => P0 P1 P2.
(** %
\begin{screen}\begin{verbatim}
ltn_pmod      : forall m d : nat, 0 < d -> m %% d < d
\end{verbatim}\end{screen}
% **)
move: (@ltn_pmod n 3).
case (n %% 3).
by [].
case.
by [].
case.
by [].
move => n0.
move/(_ erefl).
(** %
\begin{screen}
※ \verb|case (n ％％ 3)| 以降の繰り返しは, \verb=[|]= を使ってまとめて書ける.
\begin{itemize}
\item \verb=|=記号の左に最初のパートを右に次のパートの証明を書く.
\item パートの中での\verb=[|]=はさらなる\verb|case|での分割を表す.
\item \verb=[|]=の前に\verb|=>|があるので, 例えば\verb|n0|は\verb|move => n0|を意味する.
また, \verb|move /(_ erefl)|は\verb|/(_ erefl)|だけ書けば良い.
\item \verb|move /(_ erefl)|は\verb|move => H; move: (H erefl); move => {H}|と同じで, ゴールが\verb|(X -> Y) -> Z|のときの\verb|(X -> Y)|の部分を\verb|X|の証明\verb|erefl|を使って\verb|Y|に書き換える.
今の場合, \verb|X=(0<3)|, \verb|Y=(n0.+3<3)|, \verb|Z=(P n0.+3)|で,
\verb|X|の証明に\verb|erefl|を使っている.
\item \verb|by []| は \verb|//| と同じ.
\end{itemize}
\verb|Restart|で最初から証明をやり直してみる.
\end{screen}

% **)
Restart.
move => P0 P1 P2; move: (@ltn_pmod n 3).
case : (n %% 3) => [ | [ | [| n0 /(_ erefl)]]] //.
Qed.

Lemma nine n P : P 0 -> P 1 -> P 2 -> P 3 -> P 4 -> P 5 -> P 6 -> P 7 -> P 8 -> P (n %% 9).
Proof.
repeat (move => ?); move: (@ltn_pmod n 9).
case: (n %% 9) => [|[|[|[|[|[|[|[|[|n0 /(_ erefl)]]]]]]]]] //.
Qed.

Lemma dup a : (a %% 9) %% 3 = a %% 3.
Proof.
(** %
\begin{screen}\begin{verbatim}
modn_dvdm : forall m n d : nat, d ％| m -> n ％％ m = n ％[mod d]
\end{verbatim}\end{screen}
% **)
by apply (@modn_dvdm 9 a 3).
Qed.



(** %
\begin{screen}
\begin{lemma}[divneq3]
自然数 $x$が
$x \equiv 0 {\ {\bf mod}\ 3}$
を満たすとき,
$$
x = 3 \left[\frac{x}{3}\right].
$$
\end{lemma}
\end{screen}

% **)

Lemma divneq3 (x:nat): (x %% 3 = 0) -> x = (x %/ 3) * 3.
Proof.
  move => H.
(** %
\begin{screen}\begin{verbatim}
divn_eq   : forall m d : nat, m = m ％/ d * d + m ％％ d
\end{verbatim}\end{screen}
% **)
  rewrite {1}(divn_eq x 3).
  by [rewrite H].
Qed.


(** %
\begin{screen}
\begin{lemma}[inj9x]
自然数 $x$, $y$が
$9x=9y$
を満たすとき,
$$
x = y.
$$
\end{lemma}
\end{screen}

% **)


Lemma inj9x (x y:nat): x * 9 = y * 9 -> x = y.
Proof.
(** %
\begin{screen}\begin{verbatim}
introT : forall (P : Prop) (b : bool), reflect P b -> P -> b
elimT : forall (P : Prop) (b : bool), reflect P b -> b -> P
eqn_pmul2r : forall m n1 n2 : nat, 0 < m -> (n1 * m == n2 * m) = (n1 == n2)
\end{verbatim}\end{screen}
% **)
  move => H; apply (introT eqP) in H.
(** %
\begin{screen}
※ \verb|move => H; apply (introT eqP) in H.|は, 
\verb|move/eqP => H.|と同じ.
\end{screen}

% **)
  rewrite (@eqn_pmul2r 9 x y erefl) in H.
  apply (elimT eqP) in H.
  apply H.
(** %
\begin{screen}
※ \verb|apply (elimT eqP) in H.|は, 
\verb|move/eqP in H.|と同じ. \verb|move/eqP|は等号\verb|==|と\verb|=|の両方向の書き換えに用いられる.
\verb|Restart|で最初からやり直し.
\end{screen}
% **)
Restart.
move/eqP.
rewrite (@eqn_pmul2r 9 x y erefl).
move/eqP.
by [].
Qed.

Lemma asqa0 (a:nat): (a ^ 2 = 0) -> (a = 0).
Proof.
by case a.  
Qed.

Lemma asqa0m (a:nat): (a ^ 2 = 0 %[mod 3]) -> (a = 0 %[mod 3]).
Proof.
(** %
\begin{screen}\begin{verbatim}
modnXm  : forall m n a : nat, (a ％％ n) ^ m = a ^ m ％[mod n]
ltn_mod : forall m d : nat, (m ％％ d < d) = (0 < d)
\end{verbatim}\end{screen}
% **)
rewrite -modnXm.
move: (@ltn_mod a 3).
case (a %% 3) => [|[|[|n]]] //.
Qed.


Lemma absqab0 (a b:nat): (a ^ 2) + (b ^ 2) = 0 -> (a = 0) /\ (b = 0).
Proof.
move/eqP.
(** %
\begin{screen}\begin{verbatim}
addn_eq0 : forall m n : nat, (m + n == 0) = (m == 0) && (n == 0)
\end{verbatim}\end{screen}
% **)
rewrite addn_eq0.
move/andP.
elim.
move/eqP => a2.
move/eqP => b2.
apply (conj (asqa0 a a2) (asqa0 b b2)).
Qed.

Lemma absqab0m (a b:nat): (a ^ 2) + (b ^ 2) = 0 %[mod 3] -> (a = 0 %[mod 3]) /\ (b = 0 %[mod 3]).
Proof.
(** %
\begin{screen}\begin{verbatim}
modnDm : forall m n d : nat, m ％％ d + n ％％ d = m + n ％[mod d]
\end{verbatim}\end{screen}
% **)
rewrite -(modnDm (a^2) (b^2)) -(modnXm 2 3 a) -(modnXm 2 3 b).
(** %
\begin{screen}
この時点でのゴールは
{\small
\begin{verbatim}
(a ％％ 3) ^ 2 ％％ 3 + (b ％％ 3) ^ 2 ％％ 3 = 0 ％[mod 3]
                                                   -> a = 0 ％[mod 3] /\ b = 0 ％[mod 3]
\end{verbatim}
}
である. ここで, \verb|a ％％ 3|と\verb|b ％％ 3|の部分に0,1,2の全ての値を入れて具体的に計算で論証するのが次の1行である.
\end{screen}

% **)
by apply (three a); apply (three b); compute.
Qed.

(** %
\begin{screen}
\begin{lemma}[PropPmod3ab]
自然数 $a$, $b$, $c$が
$a^2 + b^2 = 3 c^2$
を満たすとき,
$$
(a \equiv 0 {\ ({\bf mod}\ 3)})
\land (b \equiv 0 {\ ({\bf mod}\ 3)}).
$$
\end{lemma}
\end{screen}

% **)


Lemma PropPmod3ab (a b c:nat): (a ^ 2) + (b ^ 2) = 3 * (c ^ 2) -> (a = 0 %[mod 3]) /\ (b = 0 %[mod 3]).
Proof.
move => H.
apply absqab0m.
rewrite H.
(** %
\begin{screen}\begin{verbatim}
modnMr : forall p d : nat, (d * p) ％％ d = 0
\end{verbatim}\end{screen}
% **)
by [rewrite (modnMr (c ^ 2) 3)].
Qed.

Lemma lemma1 (a:nat): (a = 0 %[mod 3]) -> ((a ^ 2) = 0 %[mod 9]).
Proof.
rewrite -(dup a) -(modnXm 2 9 a).
move: (@ltn_mod a 9).
by apply (nine a);compute.
Qed.

Lemma lemma2 (a b:nat): (a = 0 %[mod 3]) -> (b = 0 %[mod 3]) -> (a ^ 2) + (b ^ 2) = 0 %[mod 9].
Proof.
move => Ha Hb.
rewrite -(modnDm (a^2) (b^2)).
rewrite (lemma1 a Ha) (lemma1 b Hb).
by [compute].
Qed.

Lemma lemma3 (c:nat): 3*c = 0 %[mod 9] -> c = 0 %[mod 3].
Proof.
(** %
\begin{screen}\begin{verbatim}
modnMm : forall m n d : nat, m ％％ d * (n ％％ d) = m * n ％[mod d]
\end{verbatim}\end{screen}
% **)
rewrite -(dup c) -modnMm.
move: (@ltn_mod c 9).
by apply (nine c); compute.
Qed.
  
Lemma PropPmod3csq (a b c:nat): (a ^ 2) + (b ^ 2) = 3 * (c ^ 2) -> (c ^ 2) = 0 %[mod 3].
Proof.
move => H.
move: (PropPmod3ab a b c H).
elim => Ha Hb.
move: (lemma2 a b Ha Hb).
rewrite H => Hc.
apply (lemma3 (c^2) Hc).
Qed.

(** %
\begin{screen}
\begin{lemma}[PropPmod3c]
自然数 $a$, $b$, $c$が
$a^2 + b^2 = 3 c^2$
を満たすとき,
$$
(c \equiv 0 {\ ({\bf mod}\ 3)}).
$$
\end{lemma}
\end{screen}

% **)

Lemma PropPmod3c (a b c:nat): (a ^ 2) + (b ^ 2) = 3 * (c ^ 2) -> c = 0 %[mod 3].
Proof.
move => H.
apply (asqa0m c (PropPmod3csq a b c H)).
Qed.

(** %
\begin{screen}
\begin{lemma}[mod3lt]
自然数 $n$に対して,
$$
\left[\frac{n+1}{3}\right] \leq n.
$$
\end{lemma}
\end{screen}

% **)

Lemma mod3lt (n:nat): (n.+1 %/ 3) <= n.
Proof.
(** %
\begin{screen}\begin{verbatim}
ltn_Pdiv : forall m d : nat, 1 < d -> 0 < m -> m ％/ d < m
\end{verbatim}\end{screen}
% **)
by [apply (@ltn_Pdiv (n.+1) 3)].
Qed.

(** %
\section{帰納法の復習}

% **)

(** %
自然数(\verb|nat|)上の証明は帰納的に定義された型\verb|nat|を定義した際に
作られる証明\verb|nat_ind|を用いて行います.
ここでは, 自然数上の数学的帰納法や超限帰納法に関わる補題を$3$つ証明します.
実際には, これらの補題を明示的に利用することなく,
SsreflectのTacticである\verb|elim|のオプション指定で
超限帰納法での証明も直接行えます.
\begin{screen}\begin{verbatim}
nat_ind
     : forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P n.+1) -> forall n : nat, P n
\end{verbatim}\end{screen}

\subsection{通常の帰納法}
% **)

Check nat_ind.
(** %
\begin{screen}
\begin{lemma}[induct0]
自然数上の命題$P(n)$に対して, \\
次の$2$つの命題が成立するとき, 任意の自然数$n$に対して$P(n)$が成り立つ.
\begin{itemize}
\item $P(0)$
\item $\forall k,\, (P(k) \to P(k+1))$
\end{itemize}
\end{lemma}
\end{screen}

% **)


Lemma induct0 (n:nat) (P: nat -> Prop): (P 0) -> (forall k:nat, (P k) -> (P (k.+1))) -> (P n).
Proof.
move => P0 Pk.
apply (nat_ind P P0 Pk).
(** %
\begin{screen}
※ \verb=elim n; [apply P0|apply Pk].= と同じ.
\end{screen}
% **)
Undo 1.
elim n; [apply P0|apply Pk].
Qed.

Print induct0.

(** %
\begin{screen}
\begin{verbatim}
induct0 = 
fun (n : nat) (P : nat -> Prop) (P0 : P 0) => (nat_ind P P0)^~ n
     : forall (n : nat) (P : nat -> Prop),
       P 0 -> (forall k : nat, P k -> P k.+1) -> P n
nat_ind = 
[eta nat_rect]
     : forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P n.+1) -> forall n : nat, P n
nat_rect = 
fun (P : nat -> Type) (f : P 0) (f0 : forall n : nat, P n -> P n.+1) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | 0 => f
  | n0.+1 => f0 n0 (F n0)
  end
     : forall P : nat -> Type,
       P 0 -> (forall n : nat, P n -> P n.+1) -> forall n : nat, P n
\end{verbatim}
\end{screen}

% **)

(** %

\subsection{超限帰納法(1)}

% **)

Definition transfinite (P:nat -> Prop) (n:nat) := forall (x : nat), (x <= n) -> (P x).

Lemma transfinite0 (P:nat -> Prop): (P 0) -> (transfinite P 0).
Proof.
move => P0 n0.
(** %
\begin{screen}\begin{verbatim}
leqn0     : forall n : nat, (n <= 0) = (n == 0)
\end{verbatim}\end{screen}
% **)
rewrite leqn0.
move/eqP => H.
rewrite H.
apply P0.
(** %
\begin{screen}
上記は, 次の1行にまとめられる.
\end{screen}
% **)
Restart.
by move=> ? ?; rewrite leqn0 => /eqP ->.
Qed.

Lemma transfiniten (P:nat -> Prop) (n:nat): (transfinite P n) -> (P n).
Proof.
move => H.
(** %
\begin{screen}\begin{verbatim}
leqnn     : forall n : nat, n <= n
\end{verbatim}\end{screen}
% **)
apply (H n (leqnn n)).
Qed.

Lemma transfiniten1 (P:nat -> Prop) (n:nat):
  (transfinite P n) -> (P n.+1) -> (transfinite P n.+1).
Proof.
move => H1 Pn1 n1.
(** %
\begin{screen}\begin{verbatim}
leq_eqVlt : forall m n : nat, (m <= n) = (m == n) || (m < n)
\end{verbatim}\end{screen}
% **)
rewrite leq_eqVlt.
move/orP.
case; [by move/eqP ->|apply (H1 n1)].
Qed.

(** %
\begin{screen}
\begin{lemma}[induct1]
自然数上の命題$P(n)$に対して, \\
次の$2$つの命題が成立するとき, 任意の自然数$n$に対して$P(n)$が成り立つ.
\begin{itemize}
\item $P(0)$
\item $\forall k,\, ((P(l),\, (\forall l \leq k)) \to
(P(l),\, (\forall l \leq (k+1))))$
\end{itemize}
\end{lemma}
\end{screen}

% **)
Lemma induct1 (n:nat) (P: nat -> Prop):
  (P 0) -> (forall k:nat, (transfinite P k) -> (transfinite P (k.+1))) -> (P n).
Proof.
move => P0 Pk.
apply transfiniten.
move: Pk.
move: (transfinite0 P P0).
apply (induct0 n (transfinite P)).
(** %
\begin{screen}
※ 命題\verb|(transfinte P)|に関する帰納法は
タクティク\verb|elim|で\verb|elim: n {-2}n (leqnn n)|として始めることが出来る.
\end{screen}
% **)
Restart.
move => P0 Pk.
elim: n {-2}n (leqnn n); [apply (transfinite0 P P0)|apply Pk].
Qed.
Print induct1.
(** %
\begin{screen}
\begin{verbatim}
induct1 = 
fun (n : nat) (P : nat -> Prop) (P0 : P 0)
  (Pk : forall k : nat, transfinite P k -> transfinite P k.+1) =>
transfiniten P n (induct1x n P (transfinite0 P P0) Pk)
     : forall (n : nat) (P : nat -> Prop),
       P 0 -> (forall k : nat, transfinite P k -> transfinite P k.+1) -> P n
\end{verbatim}
\end{screen}

% **)

(** %
\subsection{超限帰納法(2)}

% **)

(** %
\begin{screen}
\begin{lemma}[induct2]
自然数上の命題$P(n)$に対して, \\
次の$2$つの命題が成立するとき, 任意の自然数$n$に対して$P(n)$が成り立つ.
\begin{itemize}
\item $P(0)$
\item $\forall k,\, (P(l),\, (\forall l \leq k)) \to P(k+1))$
\end{itemize}
\end{lemma}
\end{screen}

% **)
Lemma induct2 (n:nat) (P: nat -> Prop):
  (P 0) -> (forall k:nat, (transfinite P k) -> (P k.+1)) -> (P n).
Proof.
move => P0 H1.
apply (induct1 n P P0).
move => k Pk.
apply (transfiniten1 P k Pk (H1 k Pk)).
Qed.

(** %
\section{主定理}  

% **)

Definition defP (a b c:nat):= a ^ 2 + b ^ 2 = 3 * c ^ 2.

Definition defQ (a b c:nat):= (a %% 3 = 0)/\(b %% 3 = 0)/\(c %% 3 = 0).

(** %
\begin{screen}
\begin{theorem}[PropPtoQ]
自然数 $a$, $b$, $c$が
$a^2 + b^2 = 3 c^2$
を満たすとき,
$$
(a \equiv 0 {\ ({\bf mod}\ 3)})
\land (b \equiv 0 {\ ({\bf mod}\ 3)})
\land (c \equiv 0 {\ ({\bf mod}\ 3)}).
$$
\end{theorem}
\end{screen}

% **)


Lemma PropPtoQ (a b c:nat):(defP a b c) -> (defQ a b c).
Proof.
rewrite /defP/defQ.
move => H.
rewrite -{2}(mod0n 3) -{5}(mod0n 3) -{8}(mod0n 3).
apply (conj (proj1 (PropPmod3ab a b c H))
      (conj (proj2 (PropPmod3ab a b c H)) (PropPmod3c a b c H))).
Qed.

(** %
\begin{screen}
\begin{theorem}[PropPmod3]
自然数 $a$, $b$, $c$が
$a^2 + b^2 = 3 c^2$
を満たすとき,
$$
\left[\frac{a}{3}\right]^2
+\left[\frac{b}{3}\right]^2
= 3 \left[\frac{c}{3}\right]^2.
$$
\end{theorem}
\end{screen}

% **)

Lemma PropPmod3 (a b c:nat): (defP a b c) -> (defP (a %/3) (b %/3) (c %/3)).
Proof.
  move => H1.
  move: (PropPtoQ a b c H1).
  elim => H2.
  elim => H3 H4.
  rewrite (divneq3 a H2) (divneq3 b H3) (divneq3 c H4) in H1.
  rewrite /defP in H1.
(** %
\begin{screen}\begin{verbatim}
expnMn : forall m1 m2 n : nat, (m1 * m2) ^ n = m1 ^ n * m2 ^ n
\end{verbatim}\end{screen}
% **)
  repeat rewrite expnMn in H1.
  rewrite (_: (3^2)=9) in H1.
(** %
\begin{screen}\begin{verbatim}
mulnDl : left_distributive muln addn
mulnA  : associative muln
\end{verbatim}\end{screen}
% **)
  rewrite -mulnDl in H1.
  rewrite mulnA in H1.
  apply (inj9x  ((a %/ 3) ^ 2 + (b %/ 3) ^ 2) (3 * (c %/ 3) ^ 2) H1).
  by [].
Qed.

(** %
\begin{screen}
\begin{theorem}[defPc0]
自然数 $a$, $b$, $c$が
$a^2 + b^2 = 3 c^2$
を満たすとき,
$$
c=0.
$$
\end{theorem}
\end{screen}

% **)

Lemma PropPc0 (a b c:nat):(defP a b c) -> (c = 0).
Proof.
move: a b.
apply (induct2 c) => [//|k H1 a b Pk1].
rewrite /transfinite in H1.
(** %
\begin{screen}
※ 超限帰納法を使う. $c=0$の場合は自明.
超限帰納法のための補題\verb|induct2|を準備していなくても,
\verb|elim: c {-2}c (leqnn c).| で超限帰納法を始めることが出来る.
\end{screen}

%**)
move: (PropPmod3 a b (k.+1) Pk1) => Pmod3.
move: (mod3lt k) => Hk1.
move: (H1 (k.+1 %/ 3) Hk1 (a %/ 3) (b %/ 3) Pmod3) => Kdiv0.
move: (PropPmod3c a b k.+1 Pk1) => Kmod0.

(** %
\begin{screen}
※ 補題\verb|PropPmod3|, 補題\verb|mod3lt|と既存の仮定を用いて,
$\left[\frac{k+1}{3}\right] \leq k$ (Hk1)と
$\left[\frac{a}{3}\right]^2
+\left[\frac{b}{3}\right]^2
= 3 \left[\frac{c}{3}\right]^2$ (Pmod3)が証明出来て仮定に加えることが出来る.
そして, 帰納法の仮定(H1)から$\left[\frac{k+1}{3}\right]=0$ (Kdiv0)が求まる.
$a^2+b^2=3(k+1)^2$ (Pk1)と
PropPmod3cから$(k+1) \equiv 0 {\ ({\bf mod}\ 3)}$ (Kmod0)が求まる.
そして, 帰納過程の結論$k+1=0$を\verb|divn_eq|を用いて導く.
\begin{verbatim}
  H1 : forall x : nat, x <= k -> forall a0 b0 : nat, defP a0 b0 x -> x = 0
  Pk1 : defP a b k.+1
  Pmod3 : defP (a ％/ 3) (b ％/ 3) (k.+1 ％/ 3)
  Hk1 : k.+1 ％/ 3 <= k
  Kdiv0 : k.+1 ％/ 3 = 0
  Kmod0 : k.+1 = 0 ％[mod 3]
Lemma divn_eq m d : m = m ％/ d * d + m ％％ d.
\end{verbatim}
\end{screen}
% **)
by rewrite (divn_eq (k.+1) 3) Kdiv0 Kmod0.
Qed.

(** %
\begin{screen}
\begin{theorem}[PropPab0]
自然数 $a$, $b$が
$a^2 + b^2 = 0$
を満たすとき,
$$
a=b=0.
$$
\end{theorem}
\end{screen}

% **)

Lemma PropPab0 (a b:nat):(defP a b 0) -> (a = 0) /\ (b = 0).
Proof.
rewrite /defP.
rewrite (_:3 * 0 ^ 2 = 0).
apply absqab0.
by [compute].
Qed.

(** %
\begin{screen}
\begin{theorem}[PropPabc0]
自然数 $a$, $b$, $c$が
$a^2 + b^2 = 3 c^2$
を満たすとき,
$$
a=b=c=0.
$$
\end{theorem}
\end{screen}

% **)

Lemma PropPabc0 (a b c:nat):(defP a b c) -> (a = 0) /\ (b = 0) /\ (c = 0).
Proof.
move => Pabc.
move: (PropPc0 a b c Pabc) => C0.
rewrite C0 in Pabc.
move: (PropPab0 a b Pabc) => AB0.
apply (conj (proj1 AB0) (conj (proj2 AB0) C0)).
Qed.

(** %

\section{補足}

半径$\sqrt{3}$の円周上にある有理点, すなわち, $x^2+y^2=3$を満たす有理数$x$,
$y$を考えます. 有理数$x$と$y$の分母をそろえて, それぞれを分数
$\displaystyle x=\frac{a}{c}$,
$\displaystyle y=\frac{b}{c}$と書く事にします.
このとき, $x^2+y^2=3$は$a^2+b^2=3c^2$に対応します.
本節の考察により$a$, $b$, $c$を自然数とすると$a=b=c=0$しか存在しません.
このことは, $x^2+y^2=3$を満たす有理点が存在しないことを表します.

\section*{謝辞}
本節の内容は基本的には著者の責任でまとめていますが,
TPPmark2014\footnote{\url{https://github.com/KyushuUniversityMathematics/TPP2014/wiki}}参加者の皆様の解答, および,
TPP2014\footnote{\url{http://imi.kyushu- u.ac.jp/lasm/tpp2014/}}参加者のみなさまのご助言に基づいています. ここにみなさまへの感謝の意を表します. ありがとうございました. 



% **)