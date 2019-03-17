(* Jacques Garrigue, 2018 年 11 月 14 日 *)

(*** 単一化 ***)

(** * 1 前回の課題 *)
Module Coq4.

  Inductive even : nat -> Prop :=
    | even_O : even O
    | even_SS : forall n, even n -> even (S (S n)).

  Inductive odd : nat -> Prop :=
    | odd_1 : odd 1
    | odd_SS : forall n, odd n -> odd (S (S n)).

  Hint Constructors even odd.

  Theorem even_odd : forall n, even n -> odd (S n).
  Proof.
    intros n He.
    induction He; auto.
  Qed.

  Theorem odd_even : forall n, odd n -> even (S n).
  Proof.
    intros n Ho.
    induction Ho; auto.
  Qed.

  Theorem even_not_odd : forall n, even n -> ~odd n.
  Proof.
    intros n He Ho.
    induction He.
    inversion Ho.
    inversion Ho.
    elim IHHe.
    assumption.
  Qed.

  Theorem even_or_odd : forall m, even m \/ odd m.
  Proof.
    induction m; auto.
    destruct IHm; auto using even_odd, odd_even.
  Qed.

  Theorem odd_odd_even : forall m n, odd m -> odd n -> even (m+n).
  Proof.
    intros m n Hm Hn.
    induction Hm; simpl; auto using odd_even.
  Qed.
End Coq4.

(** * 2 単一化と自動化 *)
Require Import Arith.

Goal forall x, 1 + x = x + 1. (** Goal で名前のない定理を証明する *)
  intros.
  (** 1 + x = x + 1 *)
  Check plus_comm.
    (** : forall n m : nat, n + m = m + n *)
  apply plus_comm.
Abort.                   (** 定理を登録せずに証明を終わらせる *)

(**
ゴールと定理 [plus_comm] の字面が異なっているのに，ここでなぜ [apply] が使えるのか．
実は [apply] は複数のことをしている．
- 1. 定理の中の ∀ で量化されている変数を「単一化用の変数」に置き換える
- 2. 置き換えられた定理の結論をゴールと「単一化」する
- 3. 定理に前提があれば，「単一化」の結果を代入した前提を新しいゴールにする．

ここでいう単一化とは，（単一化用の）変数を含んだ項同士をその変数の値を定めることで同じ
ものにする．例えば，[1 + x = x + 1] と [?m+?n =?n+?m] を単一化するには，[?m = 1], [?n = x] と
定めれば良い．
[apply] で変数が定まらないと，エラーになる．しかし，[eapply] を使えば，変数が残せる．
 *)
Goal forall x y z, x + y + z = z + y + x.
  intros.
  Check eq_trans.
    (** : forall (A : Type) (x y z : A), x = y -> y = z -> x = z *)
  (**
  apply eq_trans.
    Error: Unable to find an instance for the variable y.
  *)
  eapply eq_trans.                (** y が結論に現れないので，eapply に変える *)
    (** x + y + z = ?13 *)
  apply plus_comm.
  eapply eq_trans.
  Check f_equal.
    (** : forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y *)
  apply f_equal.                                         (** [?f = plus z] *)
  apply plus_comm.
  apply plus_assoc.
Restart.                                                 (** 証明を元に戻す *)
  intros.
  rewrite plus_comm.                             (** [rewrite] も単一化を使う *)
  rewrite (plus_comm x).
  apply plus_assoc.
Abort.

(**
一階の項に関して，単一化は最適な代入を見つけてくれるという結果が知られている．
 *)

(**
- 定義 1 ある代入 σ1 が代入 σ2 より一般的であるとは，σ12 が存在し，σ2 = σ12 ◦ σ1 であることを
いう．
- 定義 2 単一化問題 {t1 = t1′, ..., tn = tn′} に対して，σ(ti) = σ(ti') であるとき，σ はその単一化問題の [単一子] だという．
 *)

(**
_定理 1_ 任意の単一化問題に対して，解が存在するときには最も一般的な単一子を返し，存在しないときにはそれを報告するアルゴリズムが存在する．
 *)

(**
具体的には，アルゴリズム U を以下の買い替え規則で定義できる．ここでは定数記号を 0 引数の関数記号と同一視する．

<<
E ∪ {f(t1,...,tn) = f(t′1,...,t′n)} → E ∪ {t1 = t′1, ..., tn = t′n}
E ∪ {f(t1,...,tn) = g(t′1,...,t′m)} → ⊥                                     f ≠ g
E ∪ {f x = t} → [t/x]E {x = t}  x ∈ vars(E) ∧ (t = y ⇒ y ∈ vars(E)) ∧ x ∉ vars(t)
E ∪ {f x = x} → E
E ∪ {f x = t} → ⊥                                                     x ∈ vars(t)
>>
 *)

(**
E が書き換えを繰り返し，書き換えられない E′ になれば，その E′ が f x1 = t′′1,..., xm = t′′m} という形であり，
それを代入 σ = [t′′1/x1,...,t′′m/x] と見なし，U(E) = σ．このときに，任意の t = t′ ∈ E について，σ(t) = σ(t′)，かつ E の単一子になる任意の σ′ について，σ が σ′ より一般的である．また，E′= ⊥ のとき，E には解がない．

上記の U は一階の項のためのものであるが，Coq はそれより強い高階単一化 1 を行っている．
しかし，この場合には最も一般的な解が存在するとは限らない．

[1] 1970 年代に高階単一化の可能性を証明した G´erard Huet は Coq の最初のプロジェクトリーダーだった
 *)
Goal
  (forall P : nat -> Prop,
      P 0 -> (forall n, P n -> P (S n)) -> forall n, P n)
  -> forall n, n + 1 = 1 + n.
  intros H n.                                  (** 全ての変数を [intro] する *)
  apply H.
Restart.
  intros H n.
  pattern n.                             (** [pattern] で正しい述語を構成する *)
  apply H.
Restart.
  intros H.                                (** [forall n] を残すとうまくいく *)
  apply H.
Abort.

(**
単一化は様々な作戦で使われている．
[apply] 以外に [induction]，[constructor]，[rewrite] や [refine] が挙げられる．
[inversion] でも単一化が使われるが，このときは特殊な単一化用の変数ではなく，通常の変数が使われる．
具体的には，[inversion H] は仮定 [H] で使われる帰納型を調べ，その型の各場合について

- 1. その場合に現れる変数を新しい変数として導入し，前提も仮定に加える
- 2. その場合の結論を H の型と単一化する
- 3. 単一化が失敗したら，この場合は否定される
- 4. 成功したら，得られた等式を仮定に加え，ゴールにその代入をかける
 *)

(** ** Hint と auto *)
(**
証明が冗長になることが多い．[auto] は簡単な規則で証明を補完しようとする．
具体的には，[auto] は 仮定や [Hint lem1 lem2 ...] で登録した定理を [apply] で適用しようとする．
これらを組み合わせて，深さ 5 の項まで作れる ([auto n] で深さ [n] にできる)．
[info auto] で使われたヒントを表示させる事もできる．
[Hint Constructors] で帰納型を登録すると，各構成子が定理として登録される．
また，[auto using lem] で一回だけヒントを追加することもできる．
[auto] で定理が適用されるために，全ての変数が定理の結論に現れる必要がある．
[eauto] を使うと [apply] が [eapply] に変わるので，決まらない変数が変数のまま残せる．
 *)

(** ** rewrite *)
(**
rewrite でも単一化が使われる.
 *)
  Section rewrite.
    Variable x : nat.
    Goal 5 + x + 0 = 5 + x.
      rewrite plus_comm.
    Abort.

(**
また, [<-] で等式を逆向きに使ったり, [,] で複数の等式を使ったりできる.
 *)
  Check plus_assoc.
  Goal 5 + x + 0 = 5 + x.
    rewrite <- plus_assoc, (plus_comm x).
  Abort.
  End rewrite.

(** ** 練習問題 2.1 以下の補題を証明せよ。*)
Section Coq5.
  Require Import List.
  Variable A : Set.
  Variable op : A -> A -> A.
  Variable e : A.

  Hypothesis op_comm : forall x y, op x y = op y x.
  Hypothesis op_assoc : forall x y z, op x (op y z) = op (op x y) z.
  Hypothesis op_neutral : forall x, op e x = x.

  Fixpoint reduce (l : list A) : A :=
    match l with
    | nil => e
    | a :: l' => op a (reduce l')
    end.

  Lemma reduce_fold : forall l, reduce l = fold_right op e l.
  Admitted.

  Lemma reduce_app : forall l1 l2, reduce (l1 ++ l2) = op (reduce l1) (reduce l2).
  Admitted.
End Coq5.
