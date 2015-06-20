(* ElementaryTactics.v 2015/01/26 Y.Mizoguchi *)
(* Original. Report140815.v *)

(** %
\section{第3回「証明の基本」}
今回は, 最も基本的な命題「等式」と「否定」の証明についての
基本的な証明の名前, また, タクティクの使い方をまとめる.

% **)

Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrfun List.

(** %

% **)

(** %
\section{等式の証明 (rewrite)}
\subsection{erefl}
最も基本的な等式の証明を与える関数は, \verb|erefl|である.
% **)

Lemma opo: 1 + 1 = 2.
Proof.
compute.
apply (erefl 2).
Qed.
Print opo.
Print erefl.

(** %
等式の証明を与える関数は $\verb|erefl|:A \to Prop$ である.
任意の型$A$の元, $a \in A$に対して,
$a = a$であることの証明を$\verb|erefl|(a)$が与える.
ここで$1+1$の計算をコンピュータに任せると,
両辺がともに$2$なので, 証明は$\verb|erefl|(2)$である.
\begin{screen}
\begin{verbatim}
opo = erefl 2
     : 1 + 1 = 2

Notation erefl := @eq_refl

Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x

For eq: Argument A is implicit and maximally inserted
For eq_refl, when applied to no arguments:
  Arguments A, x are implicit and maximally inserted
For eq_refl, when applied to 1 argument:
  Argument A is implicit
For eq: Argument scopes are [type_scope _ _]
For eq_refl: Argument scopes are [type_scope _]
\end{verbatim}
\end{screen}
% **)

(** %
\subsection{eq\_ind}
次に等式の証明で重要となるのが, \verb|eq_ind| である.

% **)

(** %
\begin{screen}
\begin{verbatim}
eq_ind = 
fun (A : Type) (x : A) => [eta eq_rect x]
     : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y

Argument A is implicit
Argument scopes are [type_scope _ _ _ _ _]
\end{verbatim}
\end{screen}
% **)

(** %
述語 $P(x)$ の証明を $F_x:P(x)$ を作ったとします.
もし, 等式 $x=y$ が成り立つ, すなわち,
等式 $x=y$ の証明($H:x=y$)があれば, 
$F_x$と$H$から,
$P(y)$の証明を作る事が出来るはずです.
$P(y)$ の証明を $F_y:P(y)$ と書くことにします.
このとき, $F_y$をCoqの関数\verb|eq_ind|を使って,
$$
F_y = (\verb|eq_ind|\  x\  P\  F_x\  y\  H)\,:\,P(y)
$$
と書きます.

\vspace{0.5cm}\noindent
ここで, $npo(x)=(x+1=2)$とすると,
$npo(1)=(1+1=2)$,
$npo(n)=(n+1=2)$ となります.
$npo(1)$の証明は, $opo:npo(1)$ ですので,
$1=n$の証明($H:1=n$)を仮定すれば,
$$
(\verb|eq_ind|\ 1\ npo\ opo\ n\ H)\,:\,npo(n)
$$
は, $npo(n)$の証明になります.
% **)

Definition npo (n:nat):Prop := (n + 1 = 2).

Lemma npo2:forall n:nat, (1 = n) -> (n + 1 = 2).
Proof.
move => n H.
apply (eq_ind 1 npo opo n H).
Qed.
Print npo.
Print npo2.

(** %
\begin{screen}
\begin{verbatim}
npo = fun n : nat => n + 1 = 2
     : nat -> Prop
npo2 = 
fun n : nat => [eta eq_ind 1 np1 opo n]
     : forall n : nat, 1 = n -> n + 1 = 2
\end{verbatim}
\end{screen}
% **)

(** %
\subsection{rewrite}
等式の書き換えには, Coq では, rewrite タクティクスを使います.
次に rewrite を使った証明と, そこで構成された関数を示す.

% **)

Lemma npo2r: forall n:nat, (1 = n) -> (n + 1 = 2).
Proof.
move => n H.
rewrite -H.
compute.
apply (erefl 2).
Qed.

Print npo2r.

(** %
\begin{screen}
\begin{verbatim}
npo2r = 
fun (n : nat) (H : 1 = n) =>
(fun _e0_ : 1 + 1 = 2 =>
 eq_ind 1 (fun _pv_ : nat => _pv_ + 1 = 2) _e0_ n H)
  (erefl 2)
     : forall n : nat, 1 = n -> n + 1 = 2
\end{verbatim}
\end{screen}

% **)


(** %
\section{構成と反対方向の性質 (inversion)}
\subsection{nat}
% **)

Print nat.

(** %
\begin{screen}
\begin{verbatim}
Inductive nat : Set :=  O : nat | S : nat -> nat
\end{verbatim}
\end{screen}

% **)

(** % 
構造体 \verb|nat| の構成子 $\verb|S|:nat \to nat$は,
$x:\verb|nat|$に対して, $S(x):\verb|nat|$. を保証する.
すなわち, \verb|nat|が帰納的加算集合(recursively enumerable set)
として定義されている.

次の補題の証明は, \verb|f_equal S| で与えられる.
\begin{lemma}
$\forall x, \forall y, \ (x=y) \to (S(x)=S(y))$
\end{lemma}

% **)
Goal forall (x y:nat), (x = y) -> ((S x) = (S y)).
move => x y.
apply (f_equal S).
Qed.

Print f_equal.

(** %
\begin{screen}
\begin{verbatim}
f_equal = 
fun (A B : Type) (f : A -> B) (x y : A) (H : x = y) =>
match H in (_ = y0) return (f x = f y0) with
| erefl => erefl (f x)
end
     : forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y
\end{verbatim}
\end{screen}
% **)

(** %
しかし, その逆, 次の補題の証明は自明ではない.
\begin{lemma}
$\forall x, \forall y, \ S(x)=S(y) \to (x=y)$
\end{lemma}

この補題を \verb|f_equal| を用いて証明するために,
$S(x)$ から, $x$ を導く関数, \verb|pre| を定義する.
% **)

Definition pre (x:nat):nat:=match x with
| O => O
| (S n) => n
end.

(** %
$H$を$S(x)=S(y)$の証明とするとき, 
\verb|(f_equal pre H)|は,
$\verb|pre|(S(x))=\verb|pre|(S(y))$,
すなわち, $x=y$の証明を与える.
% **)

Lemma ss:forall (x y:nat), (S x)=(S y) -> (x = y).
Proof.
move => x y.
apply (f_equal pre).
Qed.

Print ss.

(** %
\begin{screen}
\begin{verbatim}
ss = 
fun x y : nat => [eta f_equal pre (y:=S y)]
     : forall x y : nat, S x = S y -> x = y
\end{verbatim}
\end{screen}
% **)

(** %
この証明のための, \verb|pre|の作成などを自動で行ってくれるタクティクが,
\verb|inversion|である.
% **)

Lemma ss1:forall (x y:nat),(S x)=(S y) -> (x = y).
Proof.
move => x y H.
(** %
\begin{screen}
\begin{verbatim}
  x : nat
  y : nat
  H : S x = S y
  ============================
   x = y
\end{verbatim}
\end{screen}
%**)
inversion H.
(** %
\begin{screen}
\begin{verbatim}
  x : nat
  y : nat
  H : S x = S y
  H1 : x = y
  ============================
   y = y
\end{verbatim}
\end{screen}
%**)
apply (erefl y).
Qed.

Print ss1.

(** %
\begin{screen}
{\small
\begin{verbatim}
ss1 = 
fun (x y : nat) (H : S x = S y) =>
(@^~ (erefl (S y)))
  match H in (_ = y0) return (y0 = S y -> x = y) with
  | erefl =>
      [eta fun H1 : S x = S y =>
           [eta fun H3 : x = y => eq_ind y (eq^~ y) (erefl y) x (eq_sym H3)]
             (f_equal (fun e : nat => match e with
                                      | 0 => x
                                      | S n => n
                                      end) H1)]
  end
     : forall x y : nat, S x = S y -> x = y
\end{verbatim}
}
\end{screen}

% **)

(** %
ここで, \verb|eq_ind| が用いられているが, 今回の例では不要である.
また, \verb|eq^~| の記述の定義は以下の通り
\footnote{\url{http://ssr.msr-inria.inria.fr/doc/ssreflect-1.5/Ssreflect.ssrfun.html}}.
$$
\verb|Notation "f ^~ y" := (fun x ⇒ f x y)|
$$
% **)

(** %
\subsection{even}
% **)

(** %
偶数の集合は次のように再帰的に定義される.
% **)

Inductive even : nat -> Prop :=
  | even_0 : even O
  | even_SS : forall n, even n -> even (S (S n)).

(** %
この定義は偶数の集合を帰納的可算集合で与えている.
\verb|even_0| と \verb|even_SS| で, 
偶数を列挙することは出来るが,
与えられた自然数 $n$ を偶数かどうかを判断することは出来ない.

与えられた自然数を偶数かどうか判断するために,
より小さな自然数に対する判定が行えるようにしたい.
そこで, 与えられた自然数の$2$つ前の自然数を返す関数
\verb|pre2| を作成する.
$$
\verb|pre2|(n)=\begin{cases}
0 & \text{\ ($n \leq 2$)} \\
n-2 & \text{\ (otherwize)}
\end{cases}
$$
% **)

Definition pre2 (x:nat):nat:=match x with
| O => O
| (S n) => match n with
             | O => O
             | (S n1) => n1
           end
end.
(** %
\verb|pre2|を用いて, 次の補題が証明される.
\begin{lemma}
$\forall x, \forall y, S(S(x))=S(S(y)) \to (x = y)$
\end{lemma}

% **)

Lemma sss: forall (x y:nat), (S (S x))=(S (S y)) -> (x = y).
Proof.
move => x y.
apply (f_equal pre2).
Qed.

(** %
次に補題
\begin{lemma}
$\forall n, even(n) \to even(pre2(n))$
\end{lemma}
を考える.
% **)

Lemma evenPre2:forall (n:nat), (even n) -> (even (pre2 n)).
Proof.
move => n.
case.
compute.
apply even_0.
move => n0 H.
compute.
apply H.
Qed.

Print evenPre2.

(** %
\begin{screen}
{\small
\begin{verbatim}
evenPre2 = 
fun (n : nat) (_top_assumption_ : even n) =>
(fun (_evar_0_ : (fun (n0 : nat) (_ : even n0) => even (pre2 n0)) 0 even_0)
   (_evar_0_0 : forall (n0 : nat) (e : even n0),
                (fun (n1 : nat) (_ : even n1) => even (pre2 n1)) 
                  (S (S n0)) (even_SS n0 e)) =>
 match
   _top_assumption_ as e in (even n0)
   return ((fun (n1 : nat) (_ : even n1) => even (pre2 n1)) n0 e)
 with
 | even_0 => _evar_0_
 | even_SS x x0 => _evar_0_0 x x0
 end) even_0 (fun n0 : nat => id)
     : forall n : nat, even n -> even (pre2 n)
\end{verbatim}
}
\end{screen}
% **)

(** %
そして, \verb|evenPre2|を用いて次の補題が証明される.
\begin{lemma}
$\forall n, even(S(S(n))) \to even(n)$
\end{lemma}
% **)

Lemma evenSS:forall n, even (S (S n)) -> even n.
move=> n.
apply (evenPre2 (S (S n))).
Qed.

(** %
\section{否定の証明 (discriminate,inversion)}
\subsection{False}
% **)
Check False_rec.
(** %
\begin{screen}
\begin{verbatim}
False_rec
     : forall P : Set, False -> P
\end{verbatim}
\end{screen}

$False$に向かう関数のひとつが \verb|False_rec| である. 
この引数に$False$自身を入れることで, $False$を得ることが出来る.
では, その引数の$False$は, どうやって作るか?
$False$そのものを仮定すれば, 当たり前だが,
$False$へ向かう関数とその引数を仮定しても良い.
$\neg P = P \to False$であるから,
$P$の証明$p:P$と$\neg P$の証明$np:(\neg P)$から,
$False$の証明$np(p):False$を構成出来る.
そして, \verb|False_rec|を用いて
任意の命題$Q$が成立するという次の補題が証明される.
\begin{lemma}
$$
P \to (\neg P) \to Q.
$$
\end{lemma}

% **)

Lemma contradict : forall (P Q : Prop), P -> ~P -> Q.
Proof.
move => P Q p np.
apply (False_rec Q (np p)).
Qed.

(** %
\subsection{$x \not= y$ (discriminate)}
% **)

Check eq_ind.
(** %
$(x = y) \to False$ すなわち, $x \not= y$ の証明は,
\verb|eq_ind|を使って与える.
\begin{screen}
\begin{verbatim}
eq_ind
     : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y
\end{verbatim}
\end{screen}
% **)

(** %
\verb|eq_ind|の定義より,
\begin{center}
\verb|(@eq_ind A x P H y)|
\end{center}
は, \verb|((x = y)| $\to$ \verb|(P y))| となる.
ここで, \verb|H:(P x)| であることに注意する.
すなわち, \verb|(P x)=True|, \verb|(P y)=False|
と計算出来る関数\verb|P|については,
\verb|I:True|であるので,
\begin{center}
\verb|(@eq_ind A x P I y)|
\end{center}
は, \verb|((x = y)| $\to$ \verb|False)| を与える.
すなわち, 等式 $(x = y)$の左辺の元に対して真, 右辺の元に対して偽となる命題\verb|P|を
作成出来れば, それと\verb|eq_ind|で\verb|((x = y)| $\to$ \verb|False)|の証明を構成可能である.

$(1 \not= 0)$を考えるとき, 自然数\verb|nat|上の述語で,
値が$1$のときのみ$True$を返す述語\verb|eqone|を定義する.
% **)

Definition eqone (x:nat):Prop:=match x with
| O => False
| S n => match n with
           | O => True
           | S _ => False
         end
end.
Compute ((eqone O)::(eqone 1)::(eqone 2)::(eqone 3)::nil).

(** %
\begin{screen}
\begin{verbatim}
Compute ((eqone O)::(eqone 1)::(eqone 2)::(eqone 3)::nil).
     = False :: True :: False :: False :: nil
     : list Prop
\end{verbatim}
\end{screen}

\verb|(eqone O)=False|, \verb|(eqone 1)=True| であることに注意する.
このとき
\begin{center}
\verb|(@eq_ind nat 1 eqone I 0)|
\end{center}
が求める証明である.
% **)

Definition eqoneq:((1=O) -> (eqone O))
:=(@eq_ind nat 1 eqone I O).
Check eqoneq.

(** %
具体的には上記の証明 \verb|eqoneq|を用いて$ 1 \not 0$ が以下のように証明される.
% **)

Goal (1<>O).
Proof.
move => H.
apply (eqoneq H).
Qed.

(** %
誤った等式ごとに矛盾を導く関数(\verb|eqone|や\verb|eqoneq|など)を
\verb|eqind|を用いて構成するのは面倒である.
Coqでは, \verb|discriminate| タクティクがその関数を構成してくれる.
次に, \verb|discriminate| を使った証明と,
そこで構成された関数を示す.
% **)

Lemma onezero:(1<>O).
Proof.
move => H.
discriminate.
Qed.
Print onezero.

(** %
\begin{screen}
\begin{verbatim}
onezero = 
fun H : 1 = 0 =>
[eta [eta False_ind False]]
  (eq_ind 1 (fun e : nat => match e with
                            | 0 => False
                            | S _ => True
                            end) I 0 H)
     : 1 <> 0
\end{verbatim}
\end{screen}
% **)

(** %
\section{$\neg P(a)$ (inversion)}
% **)

(** %
$\neg P(a)$ の証明は, $P(a) \to False$ の証明に対応する.
$P(a)$を直接計算して$False$を導けない場合,
$Q:A \to Prop$で, $Q(a)=False$が計算出来,
かつ, $P(a) \to Q(a)$が証明出来る述語$Q(x)$を考える.
具体的には, $Q$の補集合が有限集合であるものであれば$Q(a)=False$は計算可能である.
$H:P(a)$, $F:\forall x, P(x) \to Q(x)$, $Q(a)=False$とすると,
$F(a):P(a) \to False$となる.
% **)

(** %
\vspace{0.5cm}\noindent
$\neg (\verb|even | 1)$を考えよう.
$\verb|even|=\{x\,|\,(\verb|even|\  x)\}$ よりも大きく, 決定可能な集合
$\verb|notone|=\{x\,|\, x\not=1\}$を定義する.
偶数の集合($\verb|even|$), および, $1$以外の集合($\verb|notone|$)は
次のように再帰的に定義される.
% **)

Definition notone (x:nat):Prop:=match x with
| O => True
| S n => match n with
           | O => False
           | (S _) => True
         end
end.

(** %
証明すべきは,
$\verb|even| \subseteq \verb|notone|$ であるが,
\verb|notone|と\verb|even|の定義から, 帰納法で証明可能である.
% **)

Lemma even_is_notone (x:nat):(even x) -> (notone x).
Proof.
 case.
 rewrite /notone.
 apply I.
 move => n H.
 rewrite /notone.
 apply I.
Qed.

(** %
さて, 
$\verb|even_is_notone|:\forall n, (\verb|even | n) \to (\verb|notone | n)$
より
$\verb|(even_is_notone 1)|:\verb|(even 1)| \to \verb|(notone 1)|$ である.
また, $\neg (\verb|even | 1):\verb|(even 1)| \to False$ であるが,
$\verb|(notone 1)| = False$であるので, 命題が証明出来る.
% **)

Lemma one_is_not_even: ~ (even 1).
Proof.
 move => H.
 apply (even_is_notone 1 H).
Qed.

Print even_is_notone.
Print one_is_not_even.

(** %
\begin{screen}
\begin{verbatim}
even_is_notone = 
fun (x : nat) (_top_assumption_ : even x) =>
(fun (_evar_0_ : (fun (n : nat) (_ : even n) => notone n) 0 even_0)
   (_evar_0_0 : forall (n : nat) (e : even n),
                (fun (n0 : nat) (_ : even n0) => notone n0) 
                  (S (S n)) (even_SS n e)) =>
 match
   _top_assumption_ as e in (even n)
   return ((fun (n0 : nat) (_ : even n0) => notone n0) n e)
 with
 | even_0 => _evar_0_
 | even_SS x0 x1 => _evar_0_0 x0 x1
 end) I (fun (n : nat) (_ : even n) => I)
     : forall x : nat, even x -> notone x

one_is_not_even = [eta even_is_notone 1]
     : ~ even 1
\end{verbatim}
\end{screen}

% **)

(** %
この\verb|notone|を探してくれるのが, \verb|inversion|である.
% **)

Lemma one_is_not_even_with_inversion: ~ (even 1).
Proof.
 move => H.
 inversion H.
Qed.

Print one_is_not_even_with_inversion.

(** %
\begin{screen}
\begin{verbatim}
one_is_not_even_with_inversion = 
fun H : even 1 =>
(@^~ (erefl 1))
  match H in (even n) return (n = 1 -> False) with
  | even_0 =>
      [eta fun H1 : 0 = 1 =>
           [eta [eta False_ind False]]
             (eq_ind 0
                (fun e : nat => match e with
                                | 0 => True
                                | S _ => False
                                end) I 1 H1)]
  | even_SS n H0 =>
      (fun H2 : S (S n) = 1 =>
       [eta [eta False_ind (even n -> False)]]
         (eq_ind (S (S n))
            (fun e : nat =>
             match e with
             | 0 => False
             | 1 => False
             | S (S _) => True
             end) I 1 H2))^~ H0
  end
     : ~ even 1
\end{verbatim}
\end{screen}

% **)

(** %

文献~\cite{bertot1998}のp.248に
"The Inner Workings of \verb|inversion|"の記述がある.

% **)
