(* DeMorgansLaw.v 2015.1.26 Y.Mizogichi*)
(* Original. Report140813.v *)

(** %
\section{第2回「ドモルガンの法則の証明」}
今回は, ブール演算の基本的な性質である「ドモルガンの法則」の証明を行う。
有限の場合(2つの集合)のドモルガンの法則は以下の4つになる.
\begin{enumerate}
\item[(1)] $(\neg A_1) \lor (\neg A_2) \to \neg (A_1 \land A_2)$
\item[(2)] $ \neg (A_1 \lor A_2) \to (\neg A_1) \land (\neg A_2)$
\item[(3)] $(\neg A_1) \land (\neg A_2) \to \neg (A_1 \lor A_2)$
\item[(4)] $\neg (A_1 \land A_2) \to (\neg A_1) \lor (\neg A_2)$
\end{enumerate}
(1)の逆の(4)の証明のみ排中律が必要となる.
\ref{demorgan:finite}節において,
\verb|Lemma DeMorgan01|で(1)を
\verb|Lemma Demorgan02|で(2)をその逆の(3)を
\verb|Lemma Demorgan03|で示す.
そして, \verb|Lemma Demorgan04|で(4)を示す.
\ref{demorgan:infinite}節においては,
無限の族に対するドモルガンの法則の中で
排中律の不要な以下の3つの命題を証明する.
\begin{enumerate}
\item[(1)] $\exists x, \neg P(x) \to \neg (\forall x, P(x))$
\item[(2)] $\neg (\exists x, P(x)) \to \forall x, \neg P(x)$
\item[(3)] $\forall x, \neg P(x) \to \neg (\exists x, P(x))$
\end{enumerate}
\verb|Lemma DeMorgan05|で(1)を
\verb|Lemma DeMorgan06|で(2)を
\verb|Lemma DeMorgan07|で(3)を示す.

% **)

Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrfun.

(** %
\section{有限の場合}\label{demorgan:finite}
% **)

Section DeMorgans_Laws.
Variables (A:Set) (P Q:A -> Prop).
Variables (A1 A2:Prop).

(** %
\subsection{直和(coproduct)}
\begin{diagram}
A_1 & \rTo^{i_1} & A_1 \oplus A_2 & \lTo^{i_2} & A_2 \\
    & \rdTo_{f_1}&  \dTo_{f_1 \bot f_2} & \ldTo_{f_2} & \\
     &          &   Y           &        & \\
\end{diagram}

集合$A_1$, $A_2$の直和集合は
$$
A_1 \oplus A_2=\{(x_1,1)\,|\, x_1 \in A_1\} \cup
\{(x_2,2)\,|\, x_2 \in A_2\}
$$
で定義される.
ここで, 
$i_k:A_k \to A_1 \oplus A_2$を
$i_k(x_k)=(x_k,k)$とする.
集合$Y$に対して, 次の同型関係がある.
$$
[A_1 \to Y] \times [A_2 \to Y] \cong [A_1 \oplus A_2 \to Y]
$$
関数$f_1:A_1 \to Y$, $f_2:A_2 \to Y$に対して,
$f_1 \bot f_2((x_k,k)) = f_k(x_k)$とし,
この1対1対応を与える同型射の左から右への関数を\verb|or_intro|,
右から左への関数を\verb|or_case|とする.
\begin{eqnarray*}
\verb|or_intro|&:&
[A_1 \to Y] \times [A_2 \to Y] \to [A_1 \oplus A_2 \to Y] \\
\verb|or_case|&:&
[A_1 \oplus A_2 \to Y] \to [A_1 \to Y] \times [A_2 \to Y] 
\end{eqnarray*}
ここで, $\verb|or_intro|(f_1,f_2)=f_1 \bot f_2$ であり,
$\verb|or_case|(g)=(g \circ i_1, g \circ i_2)$ である.

% **)

(** %
直和 $X_1 \lor X_2$ は Colimit なので,
関数の対 $(f_1:X_1 \to Y, f_2:X_2 \to Y)$ と
関数 $f_1 \bot f_2:X_1 \lor X_2 \to Y$が, 1対1に対応する.
$f_1 \bot f_2$を与える関数を \verb|or_intro| とする.
% **)
  

Lemma or_intro: forall X1 X2 Y:Prop, ((X1 -> Y) * (X2 -> Y)) -> (X1 \/ X2) -> Y.
Proof.
move => X1 X2 Y H.
elim :H.
move => H1 H2 H3.
case :H3.
apply H1.
apply H2.
Qed.

Lemma or_case: forall X1 X2 Y:Prop, ((X1 \/ X2) -> Y) -> ((X1 -> Y) * (X2 -> Y)).
Proof.
move => X1 X2 Y H.
have :X1 -> X1 \/ X2.
move => X11.
left.
apply X11.
move => X11.
have :X2 -> X1 \/ X2.
move => X22.
right.
apply X22.
move => X22.
apply pair.
move => X111.
apply (H (X11 X111)).
move => X222.
apply (H (X22 X222)).
Qed.

(** %
\subsection{$(\neg A_1) \lor (\neg A_2) \to \neg (A_1 \land A_2)$}

% **)
(** %
次のドモルガンの法則を証明する.
\begin{theorem}\label{th1}
$(\neg A_1) \lor (\neg A_2) \to \neg (A_1 \land A_2)$
\end{theorem}
直和からの関数なので, 構成する2つの関数たち
$(\neg A_1) \to \neg (A_1 \land A_2)$ と
$(\neg A_2) \to \neg (A_1 \land A_2)$ を先に考える.
$\neg A_1$は関数$f_1:A_1 \to False$,
$\neg (A_1 \land A_2)$は関数$f_p:(A_1 \land A_2) \to False$
であるので,
$f_1$が与えられたときに, $f_p$を作る方法を考えれば良い.
直積$A_1 \land A_2$には, 射影$proj_1:(A_1 \land A_2) \to A_1$が
存在するので, これと$f_1$合成することで$f_p$を得ることが出来る.
すなわち, $f_p:=f_1 \circ proj_1$ とすれば良い.
% **)

Lemma DeMorgan011: ~ A1 -> ~ (A1 /\ A2).
Proof.
move => f1. 
move => xy.
apply (f1 (proj1 xy)).
Restart.
move => f1 xy.
elim xy.
move => a1 a2.
apply f1.
apply a1.
Qed.

Lemma DeMorgan012: ~ A2 -> ~ (A1 /\ A2).
Proof.
move => f2 xy.
apply (f2 (proj2 xy)).
Qed.

(** %
出来上がった関数
 $DeMorgan011:\neg A_1 \to \neg (A_1 \land A_2)$,
 $DeMorgan012:\neg A_2 \to \neg (A_1 \land A_2)$
に対して, 
$$
DeMorgan011 \perp DeMorgan012 : 
(\neg A_1) \lor (\neg A_2) \to \neg (A_1 \land A_2)
$$
がドモルガンの法則の証明に対応する関数である.
この関数は, \verb|or_intro|を用いて構成される.

\begin{diagram}
\neg A_1 & \rTo^{or\_introl} & (\neg A_1) \lor (\neg A_2) & \lTo^{or\_intror} & \neg A_2 \\
    & \rdTo_{f_1=DeMorgan011}&  \dTo_{f_1 \bot f_2} & \ldTo_{f_2=DeMorgan012} & \\
     &          &  \neg(A_1 \land A_2)           &        & \\
\end{diagram}

% **)

Lemma DeMorgan01 : ~ A1 \/ ~ A2 -> ~ (A1 /\ A2).
Proof.
apply (or_intro (~ A1) (~ A2) (~ (A1 /\ A2)) (pair DeMorgan011 DeMorgan012)).
Qed.
Print or_intro.
Print DeMorgan011.
Print DeMorgan012.
Print DeMorgan01.

(** %
\begin{screen}
\begin{verbatim}
DeMorgan011 = 
fun (f1 : ~ A1) (xy : A1 /\ A2) => f1 (proj1 xy)
     : ~ A1 -> ~ (A1 /\ A2)
DeMorgan012 = 
fun (f2 : ~ A2) (xy : A1 /\ A2) => f2 (proj2 xy)
     : ~ A2 -> ~ (A1 /\ A2)
DeMorgan01 = 
or_intro (~ A1) (~ A2) (~ (A1 /\ A2)) (DeMorgan011, DeMorgan012)
     : ~ A1 \/ ~ A2 -> ~ (A1 /\ A2)
\end{verbatim}
\end{screen}
% **)


(** %

\subsection{直積(product)}
\begin{diagram}
A_1 & \lTo^{p_1} & A_1 \times A_2 & \rTo^{p_2} & A_2 \\
    & \luTo_{f_1}&  \uTo_{f_1 \top f_2} & \ruTo_{f_2} & \\
     &          &   X           &        & \\
\end{diagram}
集合$A_1$, $A_2$の直積は
$$
A_1 \times A_2=\{(x_1,x_2)\,|\, x_1 \in A_1, \ x_2 \in A_2\}
$$
で定義される.
ここで, $p_k:A_1 \coprod A_2 \to A_k$を$p_k(x_1,x_2=x_k$とする.

集合$X$に対して, 次の同型関係がある.
$$
[X \to A_1] \times [X \to A_2] \cong [X \to A_1 \times A_2]
$$
関数$f_1:X \to A_1$, $f_2:X \to A_2$対して,
$f_1 \top f_2(x)=(f_1(x),f_2(x))$とし, 
この1対1対応を与える同型射の左から右への関数を\verb|prod_intro|,
右から左への関数を\verb|prod_case|とする.
\begin{eqnarray*}
\verb|prod_intro|&:&
[X \to A_1] \times [X \to A_2] \to [X \to A_1 \times A_2] \\
\verb|prod_case|&:&
[X \to A_1 \times A_2] \to [X \to A_1] \times [X \to A_2]
\end{eqnarray*}
ここで, $\verb|prod_intro|(f_1,f_2)=f_1 \top f_2$ であり,
$\verb|prod_case|(g)=(p_1 \circ g, p_2 \circ g)$ である.

% **)

(** %
直積 $X_1 \land X_2$ は Limit なので,
関数の対 $(f_1:X \to X_1, f_2:X \to X_2)$ と
関数 $f_1 \top f_2:X \to X_1 \land X_2$が, 1対1に対応する.
$f_1 \top f_2$を与える関数を \verb|and_intro| とする.
% **)

Lemma and_intro: forall X1 X2 X:Prop,
((X -> X1) * (X -> X2)) -> (X -> (X1 /\ X2)).
Proof.
move => X1 X2 X H.
elim :H.
move => X11 X22 XX.
split.
apply (X11 XX).
apply (X22 XX).
Qed.

Lemma and_case: forall X1 X2 X:Prop,
(X -> (X1 /\ X2)) -> ((X -> X1) * (X -> X2)).
Proof.
move => X1 X2 X H.
split.
move => XX.
apply (proj1 (H XX)).
move => XX.
apply (proj2 (H XX)).
Qed.

(** %
\subsection{$ \neg (A_1 \lor A_2) \to (\neg A_1) \land (\neg A_2)$}
もうひとつのドモルガンの法則は以下のように定式化される.
\begin{theorem}\label{th2}
$ \neg (A_1 \lor A_2) \to (\neg A_1) \land (\neg A_2)$
\end{theorem}

% **)


Lemma DeMorgan021: ~ (A1 \/ A2) -> ~ A1.
Proof.
move => H H1.
apply (H (or_introl H1)).
Qed.

Lemma DeMorgan022: ~ (A1 \/ A2) -> ~ A2.
Proof.
move => H H1.
apply (H (or_intror H1)).
Qed.

(** %
出来上がった関数
 $DeMorgan021: \neg(A_1 \lor A_2) \to \neg A_1$,
 $DeMorgan022: \neg(A_1 \lor A_2) \to \neg A_2$
に対して,
$$
  DeMorgan021 \top DeMorgan022: \neg(A_1 \lor A_2) \to (\neg A_1 \lor \neg A_2)
$$
がドモルガンの法則の証明に対応する関数である.
この関数は \verb|and_intro| を用いて証明される.

\begin{diagram}
\neg A_1 & \lTo^{proj1} & (\neg A_1) \land (\neg A_2) & \rTo^{proj2} & \neg A_2 \\
    & \luTo_{f_1=DeMorgan021}&  \uTo_{f_1 \top f_2} & \ruTo_{f_2=DeMorgan022} & \\
     &          &  \neg (A_1 \lor A_2)           &        & \\
\end{diagram}

% **)

Theorem DeMorgan02: ~ (A1 \/ A2) -> ~ A1 /\ ~ A2.
Proof.
apply (and_intro ( ~ A1) ( ~ A2) ( ~ (A1 \/ A2)) (pair DeMorgan021 DeMorgan022)).
Qed.

Print DeMorgan021.
Print DeMorgan022.
Print DeMorgan02.

(** %
\begin{screen}
\begin{verbatim}
DeMorgan021 = 
fun (H : ~ (A1 \/ A2)) (H1 : A1) => H (or_introl H1)
     : ~ (A1 \/ A2) -> ~ A1
DeMorgan022 = 
fun (H : ~ (A1 \/ A2)) (H1 : A2) => H (or_intror H1)
     : ~ (A1 \/ A2) -> ~ A2
DeMorgan02 = 
and_intro (~ A1) (~ A2) (~ (A1 \/ A2)) (DeMorgan021, DeMorgan022)
     : ~ (A1 \/ A2) -> ~ A1 /\ ~ A2
\end{verbatim}
\end{screen}

% **)

(** %
\subsection{$(\neg A_1) \land (\neg A_2) \to \neg (A_1 \lor A_2)$}

次に, Theorem~\ref{th2}の逆の証明を考える.
\begin{theorem}
$(\neg A_1) \land (\neg A_2) \to \neg (A_1 \lor A_2)$
\end{theorem}
$\neg A_1$, $\neg A_2$の証明は, それぞれ, $False$への関数,
$f_1:A_1 \to False$, $f_2:A_2 \to False$である.
求めたい証明は, $A_1 \lor A_2$から$False$への関数なので,
これは, \verb|or_intro|を用いて構成出来る.
この方針で次の定理 \verb|DeMorgan03| を証明する.

\begin{diagram}
A_1 & \rTo^{or\_introl} & A_1 \land A_2 & \lTo^{or\_intror} & A_2 \\
    & \rdTo_{A11}&  \dTo_{A11 \bot A22} & \ldTo_{A22} & \\
     &          &   False           &        & \\
\end{diagram}

% **)

Theorem DeMorgan03: ~ A1 /\ ~ A2 -> ~ (A1 \/ A2).
Proof.
move => H1.
case H1.
move => A11 A22 H2.
apply ((or_intro A1 A2 False (pair A11 A22)) H2).
Qed.

Print DeMorgan03.

(** %
\begin{screen}
\begin{verbatim}
DeMorgan03 = 
fun H1 : ~ A1 /\ ~ A2 =>
match H1 with
| conj A11 A22 => [eta or_intro A1 A2 False (A11, A22)]
end
     : ~ A1 /\ ~ A2 -> ~ (A1 \/ A2)
\end{verbatim}
\end{screen}

% **)

(** %

\subsection{$\neg (A_1 \land A_2) \to (\neg A_1) \lor (\neg A_2)$}

排中律の逆向きの証明は二重否定の仮定が必要である.
二重否定を仮定すると, ドモルガンの法則(Theorem~\ref{th1})の逆を証明出来る.
\begin{theorem}\label{th1i}
If $\forall A, \neg\neg A \to A$, then we have
$\neg (A_1 \land A_2) \to (\neg A_1) \lor (\neg A_2)$.
\end{theorem}

まず, 二重否定を仮定した排中律の証明を行う.

% **)

Lemma excluded : forall A0, (forall A1, ~ ~A1 -> A1) -> (A0 \/ ~A0).
Proof.
move => A0 H2.
apply H2.
move => H3.
apply H3.
right.
move => H4.
apply H3.
left.
apply H4.
Qed.

Lemma ContraPositive: forall P0 Q0 : Prop, (P0 -> Q0) -> ( ~ Q0 -> ~ P0).
Proof.
move => P0 Q0 PQ NQ PP0.
apply (NQ (PQ PP0)).
Qed.

Theorem DeMorgan04 : (forall A1, ~ ~ A1 -> A1) -> ~ (A1 /\ A2) -> ( ~ A1 \/ ~ A2).
Proof.
move => H1 H2.
move: (excluded A1 H1).
(** %
\begin{screen}
\begin{verbatim}
H2 : ~ (A1 /\ A2)
============================
 A1 \/ ~ A1 -> ~ A1 \/ ~ A2
\end{verbatim}
上記の排中律を仮定したゴールに対して, \verb|case|で場合分けを行う.
\verb|A1|を仮定した場合は, \verb|~A2|, すなわち, 右側(right)を示す.
\verb|~A1|を仮定した場合は, 左側(left)が明らかに成立する.
\verb|case => AA1|は仮定した\verb|A1|または\verb|~A1|に名前を着ける.
その後, \verb=[right|by left]= と書けば, 後半, \verb|~A1|を仮定した証明は終わり,
前半, \verb|A1|を仮定した場合のみ続ければ良い.
\end{screen}
% **)
case => AA1; [right|by left].
move => AA2.
apply (H2 (conj AA1 AA2)).
(** %
\begin{screen}
\verb|case|以下の後半の証明は, 先に証明した対偶命題\verb|ContraPositive|を使えば,
\begin{verbatim}
   apply (ContraPositive A2 (A1 /\ A2) (@conj A1 A2 AA1) H2).
\end{verbatim}
で証明出来る. \verb|conj:A1 -> A2 -> A1 /\ A2| に注意する.

別の方法では, \verb|case|の行は,
\begin{verbatim}
   case => AA1; [by right => AA2; apply H2|by left].
\end{verbatim}
とすれば, 1行で証明が完成する.
\end{screen}

% **)
Qed.
Print DeMorgan04.

(** %
\begin{screen}
\begin{verbatim}
DeMorgan04 = 
fun (H1 : forall A1 : Prop, ~ ~ A1 -> A1) (H2 : ~ (A1 /\ A2)) =>
ssr_have (A1 \/ ~ A1) (excluded A1 H1)
  (fun H3 : A1 \/ ~ A1 =>
   match H3 with
   | or_introl AA1 => or_intror (fun AA2 : A2 => H2 (conj AA1 AA2))
   | or_intror H4 => or_introl H4
   end)
     : (forall A1 : Prop, ~ ~ A1 -> A1) -> ~ (A1 /\ A2) -> ~ A1 \/ ~ A2
\end{verbatim}
\end{screen}

% **)

(** %
\section{無限の場合}\label{demorgan:infinite}

有限の場合のドモルガンの法則~\label{th1}の無限の場合への拡張を考える.

\subsection{$\exists x, \neg P(x) \to \neg (\forall x, P(x))$}

\begin{theorem}
$\exists x, \neg P(x) \to \neg (\forall x, P(x))$
\end{theorem}

$\exists x:A$は無限直和に対応する. すなわち, Colimitである.
関数の族
$$
\{f_a: \neg P(a) \to Y\,|\, a \in A \}
$$
と関数 $\displaystyle \perp_{a \in A} f_a : (\exists x, \neg P(x)) \to Y$ が
1対1に対応する.
$\displaystyle \perp_{a \in A} f_a$ を与える関数を
\verb|ex_intros| とする.
% **)

Lemma ex_intros: forall Y:Prop,
(forall x, ((P x) -> False) -> Y) -> ((exists x, ((P x) -> False)) -> Y).
Proof.
move => Y fx H1.
case H1.
move => x Px.
apply (fx x).
apply Px.
Qed.

(** %
一方, $\forall x:A, P(x)$ は無限直積, すなわちLimit対象である.
その射影関数,
任意の$a \in A$に対して, $P(a)$を導く関数を \verb|projx| とする.
% **)

Lemma projx: forall a:A, (forall x:A, P x) -> (P a).
Proof.
move => a fa.
apply (fa a).
Qed.

(** %
ドモルガンの法則により直和からの関数を構成するための関数を定義する.
すなわち, $a \in A$ に対して, 関数
$f_a: \neg P(a) \to \neg (\forall x, P(x))$ を作る.
この関数を \verb|DeMorgan050|として定義する.
% **)

Lemma DeMorgan051 : forall a:A, ~ (P a) -> ~ (forall x, (P x)).
Proof.
move => a. 
move => f1. 
move => fa.
apply (f1 (projx a fa)).
Qed.

Print ex_intros.
(** %
\begin{screen}
\begin{verbatim}
ex_intros = 
fun (X Y : Prop) (fx : forall x : A, (P x -> X) -> Y)
  (H1 : exists x : A, P x -> X) =>
match H1 with
| ex_intro x Px => fx x Px
end
     : forall X Y : Prop,
       (forall x : A, (P x -> X) -> Y) -> (exists x : A, P x -> X) -> Y
\end{verbatim}
\end{screen}
% **)

Check DeMorgan051.
Check ex_intros.
Check (ex_intros _ DeMorgan051).

(** %
\begin{screen}
\begin{verbatim}
DeMorgan050
     : forall a : A, ~ P a -> ~ (forall x : A, P x)
ex_intros
     : forall Y : Prop,
       (forall x : A, (P x -> False) -> Y) ->
       (exists x : A, P x -> False) -> Y
ex_intros (~ (forall x : A, P x)) DeMorgan050
     : (exists x : A, P x -> False) -> ~ (forall x : A, P x)
\end{verbatim}
\end{screen}

最後にドモルガンの法則は,
\verb|ex_intros|に\verb|DeMorgan050|を適用して証明される.
% **)

Theorem DeMorgan05 : (exists x, ~ (P x)) -> ~ (forall x, (P x)).
Proof.
apply (ex_intros _ DeMorgan051).
Qed.

Print DeMorgan05.

(** %
\begin{screen}
\begin{verbatim}
DeMorgan05 = 
ex_intros (~ (forall x : A, P x)) DeMorgan050
     : (exists x : A, ~ P x) -> ~ (forall x : A, P x)
\end{verbatim}
\end{screen}

% **)


(** %

\subsection{$\neg (\exists x, P(x)) \to \forall x, \neg P(x)$}

もうひとつのドモルガンの法則
\begin{theorem}\label{th5}
$\neg (\exists x, P(x)) \to \forall x, \neg P(x)$
\end{theorem}
を考えてみる.

$\neg (\exists x, P(x))$の証明は
関数 $(\exists x, P(x)) \to False$であり,
関数族
$$
\{f_a:P(a) \to False\,|\, a \in A\}
$$ である.
目的とする関数は
$x:A \to P(x):Prop \to False$であるので, 
まず, \verb|ex_intros|の逆,
関数 $(\exists x, P(x))$ から $Y$ への関数を
関数族 $\{f_a:P(a) \to Y\,|\, a \in A\}$ へ分解する関数
\verb|ex_case|を作る.

% **)

Lemma ex_case: forall Y:Prop, ((exists x, (P x)) -> Y) -> (forall x:A, ((P x) -> Y)).
Proof.
move => Y H a H1.
apply H.
exists a.
apply H1.
Qed.

Print ex_case.

(** %
\begin{screen}
{\small
\begin{verbatim}
ex_case = 
fun (Y : Prop) (H : (exists x : A, P x) -> Y) (a : A) (H1 : P a) =>
H (ex_intro [eta P] a H1)
     : forall Y : Prop, ((exists x : A, P x) -> Y) -> forall a : A, P a -> Y
\end{verbatim}
}
\end{screen}

そして, 次のドモルガンの法則が証明される.
% **)

Theorem DeMorgan06 : (~ exists x, P x) -> forall x, ~ P x.
Proof.
move => H1 x Px.
apply (ex_case False H1 x).
apply Px.
Qed.

Print DeMorgan06.

(** %
証明中, \verb|H1:(~ exists x, P x)|, \verb|Px:P x|に注意する.

\begin{screen}
\begin{verbatim}
DeMorgan06 = 
fun (H1 : ~ (exists x : A, P x)) (x : A) => [eta ex_case False H1 x]
     : ~ (exists x : A, P x) -> forall x : A, ~ P x
\end{verbatim}
\end{screen}
% **)

(** %

\subsection{$\forall x, \neg P(x) \to \neg (\exists x, P(x))$}

次にTheorem~\ref{th5}の逆
\begin{theorem}\label{th6}
$\forall x, \neg P(x) \to \neg (\exists x, P(x))$
\end{theorem}
を考えてみる.
$\neg (\exists x, P(x))$の証明はColimitから
$False$への関数であるので, \verb|ex_intro|で実現可能である.
個別の証明から全体の証明を構築するように
\verb|ex_intro2|を構成する.
% **)

Lemma ex_intros2: forall Y:Prop,
(forall x, (P x) -> Y) -> ((exists x, (P x)) -> Y).
Proof.
move => Y fx H1.
case H1.
move => x Px.
apply (fx x Px).
Qed.

Theorem DeMorgan07 : (forall x, ~ P x) -> ( ~ exists x, P x).
Proof.
move => H H1.
apply (ex_intros2 False H H1).
Qed.
