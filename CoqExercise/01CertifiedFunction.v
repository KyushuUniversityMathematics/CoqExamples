(* CertifiedFunction.v 2015/01/26 Y.Mizoguchi *)
(* Original. Report140810.v *)

(** %
\section{第1回「プログラム関数の同値性の証明」}
今回は, $1+2+\cdots +n$ 
繰り返し計算(再帰呼び出し)で計算する関数
$\displaystyle sumA(n) = \sum_{k=0}^{n} k$と
総和の公式を用いて計算する関数$\displaystyle sumB(n) = \frac{n(n+1)}{2}$
に対して, 2つの関数の値が等しいこと, すなわち
\begin{theorem}
Let $n \in \mathbf{N}$.
Define two functions $sumA(n)$ and $sumB(n)$ as follows:
\begin{eqnarray*}
sumA(n) &=& \sum_{k=0}^{n} k, \\
sumB(n) &=& \frac{n(n+1)}{2}.
\end{eqnarray*}
Then, $sumA(n)=sumB(n)$ for any $n$. \\
Where $\displaystyle \sum_{k=0}^{0} k = 0$ and
$\displaystyle \sum_{k=0}^{n+1} k = (n+1) + \sum_{k=0}^{n} k$
for $n \in \mathbf{N}$.
\end{theorem}
を証明する.

そして, 証明された関数$sumA(n)$と$sumB(n)$をHaskell言語の関数として出力する.
この2つのHaskell関数は同じ値を返すことが形式的に証明されていることになる.

% **)

Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrfun Ssreflect.ssrnat MathComp.div List.

(** %
\section{自然数の性質}

% **)

(** %
自然数の集合は帰納的に定義される.

\begin{screen}
\begin{verbatim}
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.
\end{verbatim}
\end{screen}

加法や乗法などの自然数上の演算は帰納的に定義される.

\begin{screen}
\begin{verbatim}
Fixpoint plus (n m:nat) : nat :=
  match n with
  | O => m
  | S p => S (p + m)
  end
\end{verbatim}
\end{screen}

わかりやすい記法を定義する.

\begin{screen}
\begin{verbatim}
Notation succn := Datatypes.S.
Notation "n .+1" := (succn n)
Notation "m + n" := (plus m n)
\end{verbatim}
\end{screen}

% **)

(** %

加法や乗法の性質は帰納的に証明される.
以下に, 基本的な補題の例を列挙する.

\begin{screen}
\begin{verbatim}
Lemma add0n : forall n:nat, 0 + n = n.
Lemma addn0 : forall n:nat, n + 0 = n.
Lemma addSn: forall m n:nat, m.+1 + n = (m + n).+1.
Lemma addnS: forall m n:nat, m + n.+1 = (m + n).+1.
Lemma addnC: forall n m:nat, m + n = n + m.
\end{verbatim}
\end{screen}

\verb|add0n|, \verb|addnS|と\verb|addSn|について,
自分で証明してみる.
関数定義に従い式を展開することで証明出来る.

% **)

Lemma my_add0n: forall n:nat, 0 + n = n.
Proof.
  move => n.
  rewrite /addn/addn_rec/plus.
  apply erefl.
Restart.
  by [].
Qed.


Lemma my_addSn: forall m n:nat, m.+1 + n = (m + n).+1.
Proof.
  move => m n.
  rewrite /addn/addn_rec/plus.
  fold plus.
  apply erefl.
Restart.
  by [].
Qed.

Lemma my_addnS: forall m n:nat, m + n.+1 = (m + n).+1.
Proof.
  elim.
  move => n.
  rewrite !add0n.
  apply erefl.
  move => n H n0.
  rewrite !addSn.
  rewrite H.
  apply erefl.
Restart.
  by [].
Qed.

(** %
次に, 交換法則の証明である\verb|addnC|を
\verb|my_addnC|という名前で, 自分で帰納法を使って
証明してみる.

% **)

Lemma my_addnC: forall n m:nat, m + n = n + m.
Proof.
  move => n m.
  elim m.
  rewrite addn0 add0n.
  apply erefl.
  move => n0 H1.
  rewrite addSn.
  rewrite H1.
  rewrite -addnS.
  apply erefl.
Restart.
  move => n m.
  ring.
Qed.

(** %
\verb|Lemma|で定める名前は
命題の名前ではなく, 証明の名前です.
命題の名前は\verb|Definition|で定めます.

% **)

Definition my_addC:=forall n m:nat, m + n = n + m.
Print my_addC.

(** %
\begin{screen}\begin{verbatim}
my_addC = forall n m : nat, m + n = n + m : Prop
\end{verbatim}\end{screen}

% **)
Goal my_addC.
move => n m.
apply (addnC m n).
Qed.
Goal my_addC.
apply /my_addnC.
Qed.

(** %
一旦, 自然数上で成立する演算の性質がわかると,
その性質の定理を用いれば帰納法を用いることなく
複雑な証明を構成することが出来る.
また, 数式を簡潔な方向に変換して適用する定理も
探して証明するタクティクと呼ばれる手続きがある(\verb|ring|など).

% **)

Lemma lemma1: forall n:nat, (n.+1)*2 + (n * (n.+1)) = (n.+1 * (n.+2)).
Proof.
  move => n.
  ring.
Qed.

(** %
\begin{screen}
\begin{verbatim}
Lemma muln_divA d m n : d ％| n -> m * (n ％/ d) = m * n ％/ d.
Lemma dvdnn m : m ％| m.
Lemma muln1 n: n * 1 = n.
Lemma dvdn_mull d m n : d ％| n -> d ％| m * n.
Lemma divnDl m n d : d ％| m -> (m + n) ％/ d = m ％/ d + n ％/ d.
\end{verbatim}
\end{screen}
% **)

Lemma lemma2: forall n:nat, (n.+1 * 2) %/ 2 = n.+1.
Proof.
  move => n.
  rewrite -(muln_divA (n.+1)).
  rewrite (divnn 2).
  simpl.
  by [rewrite muln1].
  apply (dvdnn 2).
Qed.

Lemma lemma3: forall n:nat, 2 %| (n.+1 * 2).
Proof.
  move => n.
  apply dvdn_mull.
  apply (dvdnn 2).
(** %
\begin{screen}
上記2行は,
\verb|apply (@dvdn_mull 2 (n.+1) 2 (dvdnn 2)).|でも良い.
\end{screen}
% **)
Qed.

Lemma lemma4: forall n:nat, n.+1 + (n * n.+1) %/ 2 = (n.+1 * n.+2) %/ 2.
Proof.
  move => n.
  rewrite -lemma1.
  rewrite (divnDl (n*n.+1) (lemma3 n)).  
  by [rewrite lemma2].
Qed.

(** %
\section{関数定義}
ここでは, 関数$sumA(n)$と$sumB(n)$の定義を行う.
定義の後, Coqシステム内でも \verb|Compute| で関数の値の例を計算して確認しておく.

% **)
Fixpoint sumA (n:nat) :=
match n with
| O => 0
| p.+1 => (p.+1) + sumA p
end.

Compute (sumA 3).
Compute (sumA 5).

(** %
\begin{screen}\begin{verbatim}
Compute (sumA 3).
     = 6
     : nat
Compute (sumA 5).
     = 15
     : nat
\end{verbatim}\end{screen}

% **)


Definition sumB (n:nat) := ((n * (n.+1)) %/ 2).

Compute (sumB 3).
Compute (sumB 5).

(** %
\begin{screen}\begin{verbatim}
Compute (sumB 3).
     = 6
     : nat
Compute (sumB 5).
     = 15
     : nat
\end{verbatim}\end{screen}

% **)

(** %
\verb|Set Printing All| とすることで, 記号(\verb|*|や\verb|％/|など)が
定義関数名で表示される. 例えば, \verb|％/|は\verb|divn|という関数で
定義されていることがわかる. また, \verb|Print half|などとすることで
関数定義を見ることが出来る.
% **)

Print sumA.
Print sumB.
Set Printing All.
Print sumB.
Unset Printing All.
Print half.


(** %
\begin{screen}
\begin{verbatim}
sumA = 
fix sumA (n : nat) : nat := match n with
                            | 0 => 0
                            | p.+1 => p.+1 + sumA p
                            end
     : nat -> nat
sumB = fun n : nat => (n * n.+1) ％/ 2
     : nat -> nat
sumB = fun n : nat => divn (muln n (S n)) (S (S O))
     : nat -> nat
half = 
fix half (n : nat) : nat :=
  match n with
  | 0 => n
  | n'.+1 => uphalf n'
  end
with uphalf (n : nat) : nat :=
  match n with
  | 0 => n
  | n'.+1 => (half n').+1
  end
for half
     : nat -> nat
\end{verbatim}
\end{screen}

上で定義した補題たちを使って, 最後に主定理を証明する.

% **)

Theorem sumAB: forall n:nat, (sumA n) = (sumB n).
Proof.
move => n.
elim n.
by [compute].
move => n0 H.
rewrite /sumA.
fold sumA.
rewrite H.
rewrite /sumB.
apply lemma4.
(** %
\begin{screen}
\verb|move => n. elim n. by [compute]. move => n0 H.|は, \\
\verb-elim => [//|n0 H].-と書ける.\\
\verb|rewrite /sumA; fold sumA|は \verb|simpl| で行える.
\end{screen}

% **)
Restart.
elim => [//|n0 H].
simpl; rewrite H /sumB -lemma4 //.
Qed.

(** %
\section{Haskell関数出力}

証明された関数 $sumA$ と $sumB$ を \verb|Extraction| を用いて,
ファイル \verb|"sumA.hs"| にHaskell言語の関数として出力する.
出力前のおまじないとして, いくつか(\verb|list|, \verb|symbol|,
\verb|bool|, \verb|nat|)の型定義が必要.
そして, 出力されたファイル中の1行 \verb|import qualified GHC.Base| を型定義文の上へ移動する必要がある.
\begin{screen}
\begin{verbatim}
import qualified Prelude

import qualified GHC.Base <-- (Moved to)
unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
-- import qualified GHC.Base <-- (Moved from)
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif
\end{verbatim}
\end{screen}
% **)

Extraction Language Haskell.


Extract Inductive list => "([])" ["[]" "(:)"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive nat => "Prelude.Int" ["0" "Prelude.succ"] "(\fO fS n -> if (n Prelude.== 0) then fO () else fS (n Prelude.- 1))".

Extraction "sumA.hs" sumA sumB.

(** %
出力されたHaskell関数のファイルを実行してみる.
\begin{screen}
\begin{verbatim}
ym$ ghci sumA.hs
GHCi, version 7.6.3: http://www.haskell.org/ghc/  :? for help
[1 of 1] Compiling SumA             ( sumA.hs, interpreted )
Ok, modules loaded: SumA.
*SumA> sumA 5
15
*SumA> sumB 5
15
*SumA> :q
\end{verbatim}
\end{screen}

出力されたHaskell関数定義文は, 以下のようになる.

\begin{screen}
\begin{verbatim}
sumA :: Prelude.Int -> Prelude.Int
sumA n =
  (\fO fS n -> if (n Prelude.== 0) then fO () else fS (n Prelude.- 1))
    (\_ ->
    0)
    (\p ->
    addn (Prelude.succ p) (sumA p))
    n
sumB :: Prelude.Int -> Prelude.Int
sumB n =
  divn (muln n (Prelude.succ n)) (Prelude.succ (Prelude.succ 0))
\end{verbatim}
\end{screen}

% **)

