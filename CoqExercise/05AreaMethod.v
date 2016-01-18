(* 05AreaMethod.v 2016/01/14 Y.Mizoguchi *)
(* Original. th6-6and40-20150605-2.v *)

Require Import AreaMethod.area_method Ssreflect.ssreflect.

(** %
\section{第5回「初等幾何の面積法による証明」}

面積法は初等幾何の性質を線分の長さ, 三角形, 四角形の面積, ピタゴラス差分などの
幾何学的量に基づく比の方程式で表現し, 式変形を用いて証明を行う手法である.
ここでは, \cite{chou:1994}にある初等幾何学の例題を
面積法のCoqによる実装である\cite{narboux:2004,quaresma:2009}を使って解く例を紹介する.

\section{AreaMethodライブラリの実装}
Coqによる面積法の実装は, Julien Narbouxらによって行われている\cite{narboux:2004}.
以下は, MacPortsのCoq8.4pl6によるAreaMethodライブラリ実装例である.
\begin{quote}
\begin{verbatim}
git clone https://gforge.inria.fr/git/coq-contribs/area-method.git
cd area-method
make
sudo make install
\end{verbatim}
\end{quote}
で, \verb|/opt/local/lib/coq/user-contrib/AreaMethod| に実装される.
再実装時は上記ディレクトリを削除してから, \verb|make|を行う.

\section{Cevaの定理の証明}
% **)

(** %
\begin{screen}
\begin{theorem}
Let $ABC$ a triangle,
$O$ a point in a triangle $ABC$.
Let $L$ ($M$, $N$) be a point on the side
$BC$ ($CA$, $AB$) 
passing through a line $AO$ ($BO$, $CO$),
respectively.
Then,
$$
\frac{OL}{AL} + \frac{OM}{BM} + \frac{ON}{CN} = 1.
$$
\end{theorem}
\begin{center}
\includegraphics[width=5.0cm]{./05fig1.eps}
\end{center}
\end{screen}
% **)

(** %
\begin{eqnarray}
&& \frac{\overline{OL}}{\overline{AL}}
+ \frac{\overline{OM}}{\overline{BM}}
+ \frac{\overline{ON}}{\overline{CN}}=1\\
&\Leftrightarrow &
\frac{S_{OBC}}{S_{ABC}}
+ \frac{S_{OAC}}{S_{BAC}}
+ \frac{S_{OBA}}{S_{CBA}}=1\\
&\Leftrightarrow &
\frac{S_{CBO}}{S_{BAC}}
+ \frac{S_{COA}}{S_{BAC}}
+ \frac{S_{OBA}}{S_{BAC}}=1\\
&\Leftrightarrow &
\frac{(S_{CBO}+S_{COA}+S_{OBA})}{S_{BAC}}=1\\
&\Leftrightarrow &
\frac{S_{BAC}}{S_{BAC}}=1
\end{eqnarray}
% **)


Variable A B C L M N O : Point.
Hypothesis h0 : inter_ll L B C A O.
Hypothesis h1 : inter_ll N B A C O.
Hypothesis h2 : inter_ll M A C B O.
Hypothesis hAL : A <> L.
Hypothesis hBM : B <> M.
Hypothesis hCN : C <> N.
Hypothesis hOAL : parallel O L A L.
Hypothesis hOMB : parallel O M B M.
Hypothesis hONC : parallel O N C N.

Lemma lemma01: S B A C <> 0.
Proof.
apply (aux_co_side_2 A C B O M hBM h2).
Qed.

Lemma lemma02: (S C B O + S C O A + S O B A) / S B A C = 1.
Proof.
rewrite - (A5 C B A O) - (A3a B A C) //.
rewrite (simp_frac_1 (S B A C) lemma01) //.
Qed.

Lemma lemma03:
(S C B O + S C O A) / S B A C + S O B A / S B A C = 1.
Proof.
rewrite (same_denom_add_1  (S C B O + S C O A) (S B A C) (S O B A) (S B A C) lemma01 lemma01).
rewrite - (Fmult_Fplus_distr_r (S C B O + S C O A) (S O B A) (S B A C)).
rewrite (simp_frac_9  (S B A C) (S C B O + S C O A + S O B A) (S B A C)
                      (nonzeromult (S B A C) (S B A C) lemma01 lemma01)).
apply lemma02.
Qed.

Lemma lemma04:
S B O C / S B A C + S O A C / S B A C + S O B A / S B A C = 1.
Proof.
rewrite (A3a B O C)  (A3a O A C).
rewrite  (same_denom_add_1 (S C B O) (S B A C) (S C O A) (S B A C) lemma01 lemma01).
rewrite  - (Fmult_Fplus_distr_r (S C B O) (S C O A) (S B A C)).
rewrite (simp_frac_9 (S B A C) (S C B O + S C O A) (S B A C)
           (nonzeromult (S B A C) (S B A C) lemma01 lemma01)).
apply lemma03.
Qed.

Lemma lemma05:
S O B C / S A B C + S O A C / S B A C + S O B A / S C B A = 1.
Proof. 
rewrite (A3a B A C) !(A3a C B A) !(A3a A C B) (A3b O B C) (A3b A B C).
rewrite (simp_frac_14 (S B O C) (- S B A C) (opzero (S B A C) lemma01))
        (simp_frac_16 (S B O C) (S B A C) (opzero (S B A C) lemma01))
        simp_12.
apply lemma04.
Qed.

Theorem ceva :
  O ** L / A ** L + O ** M / B ** M + O ** N / C ** N = 1.
Proof.
rewrite (co_side_elim_2 B C A O L hAL h0)
            (co_side_elim_2 A C B O M hBM h2)
            (co_side_elim_2 B A C O N hCN h1).
apply lemma05.
(** %
\begin{screen}
(注.) \verb|area_method|タクティクを使えば, 次の2行で証明出来る.
\end{screen}

% **)
Restart.
move: A B C L M N O h0 h1 h2 hAL hBM hCN hOAL hOMB hONC.
area_method.
Qed.

(** %
\section{補足}

\begin{screen}
点$A$ と　直線上の3点 $B$, $C$, $D$ が存在するとき,
${\cal{S}}_{ABC}$と${\cal{S}}_{ABD}$の面積の比は
${\overline{BC}}$と${\overline{BD}}$の比に等しい.
\end{screen}
% **)
Lemma co_side_semi: forall A B C D: Point,
~ Col A B D ->  Col B C D -> (B ** C / B ** D) = (S A B C / S A B D).
Proof.
move => A B C D hnD hC.
apply (A6 B C D A (notcolnotegal_2 A B D hnD) hnD hC).
(** %
\begin{screen}\begin{verbatim}
A6 : forall A B C P : Point,
       A <> C ->
       ~ Col P A C -> Col A B C -> A ** B / A ** C = S P A B / S P A C

 notcalnotegal_2 :  forall A B C:Point, ~ Col A B C -> B <> C
\end{verbatim}\end{screen}
% **) 
Qed.

(** %
\begin{screen}
3点 $A$, $B$, $C$ が直線上にないとき,
線分$BC$とその中点$D$が存在するなら,
$\displaystyle \frac{{\cal{S}}_{ABD}}{{\cal{S}}_{ABC}}=\frac{1}{2}$
\end{screen}
% **)

Lemma mid_double: forall A B C D: Point,
~ Col A B C -> mid_point D B C -> B <> D -> (1 / 2) = (S A B D / S A B C).
Proof.
move => A B C D ncolABC mpDBC neBD.
(** %
\begin{screen}\begin{verbatim}
midpoint_ratio_1  : forall O B D : Point,
       mid_point O B D -> B <> D -> B ** O / B ** D = 1 / 2
\end{verbatim}\end{screen}
% **)
rewrite -(midpoint_ratio_1 D B C mpDBC (notcolnotegal_2 A B C ncolABC)).
apply (co_side_semi A B D C ncolABC (col_2 B C D (proj1 mpDBC))).
(** %
\begin{screen}\begin{verbatim}
col_2:  forall A B C : Point, Col A B C -> Col A C B
\end{verbatim}\end{screen}
% **)
Qed.

(** %
\bibliographystyle{jalpha}
\bibliography{CoqPapers}

% **)