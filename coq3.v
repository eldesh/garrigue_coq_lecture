(* Jacques Garrigue, 2018 年 10 月 17 日 *)

(*** 述語論理と帰納法 ***)

(**
 * 1 述語論理
 **)

(*
 * 前回見た命題論理は，推論の概念を捉えているが，具体的な対象に対して議論することができない．
 * 我々が一般的に使う論理はその拡張である述語論理になる．
 *)

(**
 * 論理式 論理式は以下の結合子から定義される．
 * t    ::= x                 項変数
 *        | c                 項定数
 *        | f(t1, . . . , tn) 項関数
 * P, Q ::= . . .             命題
 *        | p(t1, . . . , tn) 述語
 *        | ∀ x.P             全称
 *        | ∃ x.P             存在
 *        | t1 = t2           等価性
 **)

(**
 * 導出規則 命題論理の導出規則に以下の規則を加える．
 *
 *        ∆ ⊢ P x ∉ 2 fv(∆)
 * ∀ 導入 -------------------
 *        ∆ ⊢ ∀ x.P
 *
 *        ∆ ⊢ ∀ x.P
 * ∀ 除去 ------------
 *        ∆ ⊢ [t/x]P
 *
 * 反射律  ∆ ⊢ t = t
 *
 *        ∆ ⊢ [t/x]P
 * ∃ 導入 -----------
 *        ∆ ⊢ ∃ x.P
 *
 *        ∆ ⊢ ∃ x.P  ∆,P ⊢ Q  x ∉ fv(∆, Q)
 * ∃ 除去 ---------------------------------
 *        ∆ ⊢ Q
 *
 *        ∆ ⊢ [t1/x]P  ∆ ⊢ t1 = t2
 * 代入   -------------------------
 *        ∆ ⊢ [t2/x]P
 **)

(*
 * ここで自由変数 fv(P) と代入が利用される．
 * fv(x) = {x}  fv(c) = ∅            fv(f(t1, . . . , tn)) = ⋓ fv(ti)
 * fv(True) = fv(False) = fv(X) = ∅  fv(p(t1, . . . , tn)) = ⋓ fv(ti)
 * fv(P ⊃ Q) = fv(P ∧ Q) = fv(P ∨ Q) = fv(P) ∪ fv(Q)
 * fv(∀ x.P) = fv(∃ x.P) = fv(P) ∖ {x}
 *)

(*
 * [t/x]x = t [t/x]y = y
 * [t/x]c = c [t/x]f(t1, . . . , tn) = f([t/x]t1, . . . , [t/x]tn)
 * [t/x]True = True [t/x]False = False [t/x]X = X
 * [t/x](P ⊃ Q) = [t/x]P ⊃ [t/x]Q                           ∧,∨ も同様
 * [t/x]p(t1, . . . , tn) = p([t/x]t1, . . . , [t/x]tn)
 * [t/x] ∀ y.P = ∀ y.[t/x]P (y ∉ fv(t))     [t/x] ∀ x.P = ∀ x.P
 * [t/x] ∃ y.P = ∃ y.[t/x]P (y ∉ fv(t))     [t/x] ∃ x.P = ∃ x.P
 *)

(**
 * 導出の例
 * ∀ x.human(x) ⊃ mortal(x) ⊢ ∀ x.human(x) ⊃ mortal(x)
 * ---------------------------------------------------
 * ∀ x.human(x) ⊃ mortal(x) ⊢ human(S) ⊃ mortal(S)      human(S) ⊢ human(S)
 * ------------------------------------------------------------------------
 *              ∀ x.human(x) ⊃ mortal(x), human(S) ⊢ mortal(S)
 **)

(**
 * Coq との対応
 *
 * Coq では項は Set に属する型，命題は Prop にそれぞれ入るが，扱いは同じである．
 **)

(**
 * 抽象と適用はあらゆる種類のものに対してできる．
 *
 * 抽象
 *      Γ,X:S ⊢ M:T  Γ ⊢ ∀ X:S,T:Type
 *      ------------------------------
 *      Γ ⊢ fun X:S ⇒ M : ∀ X:S,T
 * 適用
 *      Γ ⊢ M:∀ X:S,T  Γ ⊢ A:S
 *      ----------------------
 *      Γ ⊢ M A:[A/X]T
 *
 * Γ ⊢ Set:Type
 *
 * Γ ⊢ A:Set
 * ----------
 * Γ ⊢ A:Type
 *
 * Γ ⊢ A:S Γ,X:A ⊢ B:Set
 * --------------------- S ∈ {Set, Prop}
 * Γ ⊢ ∀ X:A, B:Set
 *
 * Γ ⊢ Prop:Type
 *
 * Γ ⊢ A:Prop
 * ----------
 * Γ ⊢ A:Type
 *
 * Γ ⊢ A:S  Γ,X:A ⊢ B:Prop   S ∈ {Set, Prop}
 * ----------------------- ∨
 * Γ ⊢ ∀ X:A, B:Prop         A ∈ {Set, Prop}
 *
 *)

(*
 * この抽象と適用は普通の関数の抽象と適用の代わりに使える．
 * そもそも A → B は ∀ X:A,B の略記法でしかない．
 *
 * 上の導出の例は適用 2 回でできる．
 *)
Section Socrates.

Variable A : Set.
Variables human mortal : A -> Prop.
Variable socrates : A.

Hypothesis hm : forall x, human x -> mortal x.
Hypothesis hs : human socrates.

Theorem ms : mortal socrates.
Proof.
  apply (hm socrates).
  assumption.
Qed.
Print ms.
(*
  ms = hm socrates hs
     : mortal socrates
 *)

End Socrates.

(*
 * ∀ と ∃ の間に De Morgan の法則がなりたつ．
 * 前回と同様に，∃ を導出しようとしたときに classic を使わなければならない．
 *)
Section Laws.

Variables (A:Set) (P Q:A->Prop).

Lemma DeMorgan2 : (~ exists x, P x) -> forall x, ~ P x.
Proof.
  intros N x Px.
  apply N.
  exists x.
  apply Px.
Qed.

Theorem exists_or : (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros H.
  destruct H as [x [p|q]]. (* 中まで破壊 *)
  left. exists x. assumption.
  right. exists x. assumption.
Qed.

Hypothesis classic : forall P, ~~P -> P.

Lemma DeMorgan2' : (~ forall x, P x) -> exists x, ~ P x.
Proof.
  intros np.
  apply classic.
  intros nen.
  apply np; clear np.
  intros a; apply classic.
  intros np.
  apply nen.
  exists a; assumption.
Qed.

End Laws.

(**
 * 練習問題 1.1 以下の定理を Coq で証明せよ．
 *)
Section Coq3.
  Variable A : Set.
  Variable R : A -> A -> Prop.
  Variables P Q : A -> Prop.

  Theorem exists_postpone :
    (exists x, forall y, R x y) -> (forall y, exists x, R x y).
  Proof. Admitted.

  Theorem or_exists : (exists x, P x) \/ (exists x, Q x) -> exists x, P x \/ Q x.
  Proof. Admitted.

  Hypothesis classic : forall P, ~~P -> P.
  Theorem remove_c : forall a,
      (forall x y, Q x -> Q y) ->
      (forall c, ((exists x, P x) -> P c) -> Q c) -> Q a.
  Proof. Admitted.

End Coq3.

(**
 * 2 帰納法
 **)

(*
 * Coq でデータ型を定義すると，自動的に帰納法の原理が生成される．
 *)
Module MyNat.
Inductive nat : Set := O : nat | S : nat -> nat.
(*
  nat is defined
  nat_rect is defined
  nat_ind is defined
  nat_rec is defined
 *)
Check nat_ind.
(*
  nat_ind
  : forall P : nat -> Prop,
    P O ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n
 *)

(*
 * もっと分かりやすく書くと，nat ind の型は
 *   ∀P, P 0 → (∀n, P n → P (S n)) → (∀n, P n)
 * である．
 * 即ち P は 0 でなりたち，任意の n について P が n でなりたてば，n + 1 でもなりたつこ
とが証明できれば，任意の n について P がなりたつ．
 * ちなみに，nat rec の定義を見ると，
 *)
Check nat_rec.
(*
  nat_rec
       : forall P : nat -> Set,
         P O ->
         (forall n : nat, P n -> P (S n)) ->
         forall n : nat, P n
 *)

(*
 * P が Prop ではなく Set を返すこと以外，全く同じである．
 * 本当の定義を見ると，
 *)
Print nat_rect.
(*
  nat_rect =
  fun (P : nat -> Type) (f : P O) (f0 : forall n : nat, P n -> P (S n)) =>
  fix F (n : nat) : P n :=
    match n as n0 return (P n0) with
    | O => f
    | S n0 => f0 n0 (F n0)
    end
 *)
(*
 * 実は普通の再帰関数同様，fix と match を使って定義されている．
 *)
End MyNat. (* 普通の nat に戻る *)

Definition plus' : nat -> nat -> nat.
  intros m n.
  induction m.
  exact n.       (* n を返す *)
  exact (S IHm). (* 帰納法によって得られた IHm の後者を返す *)
Defined.         (* 計算を可能にするために Defined で閉じる *)
Print plus'.
(*
   fun m n : nat => nat_rec (fun _ : nat => nat) n (fun _ IHm : nat => S IHm) m
 *)
Eval compute in plus' 2 3.
(*
  = 5
  : N
 *)

Lemma plus_assoc : forall m n p, m + (n + p) = (m + n) + p.
Proof.
  intros m n p.
  induction m.
  simpl.                                  (* 計算する *)
  SearchPattern (?X = ?X).                (* 反射律を調べる *)
  (* eq_refl: forall (A : Type) (x : A), x = x *)
  apply eq_refl.
  simpl.
  rewrite IHm.                            (* 代入を行う *)
  reflexivity.                            (* apply eq_refl と同じ *)
Qed.

(**
 * 練習問題 2.1 以下の定理を証明せよ．
 **)
Theorem plus_0 : forall n, n + 0 = n.
Proof. Admitted.

Theorem plus_m_Sn : forall m n, m + (S n) = S (m + n).
Proof. Admitted.

Theorem plus_comm : forall m n, m + n = n + m.
Proof. Admitted.

Theorem plus_distr : forall m n p, (m + n) * p = m * p + n * p.
Proof. Admitted.

Theorem mult_assoc : forall m n p, m * (n * p) = (m * n) * p.
Proof. Admitted.

