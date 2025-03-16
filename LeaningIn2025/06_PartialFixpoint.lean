/-!
部分固定点
=================

再帰関数定義メカニズムの最新の追加：`partial_fixpoint`。

終了証明は不要です！
これにより非終了関数仕様が可能になります！

主にソフトウェアやアルゴリズムの検証時に有用です。
-/

/-
終了証明が難しい関数の例：
-/

def f91 (n : Nat) : Option Nat :=
  if n > 100
    then pure (n - 10)
    else f91 (n + 11) >>= f91
partial_fixpoint

/-
`partial_fixpoint`のルール（簡略化）：

* 関数の型は`Option`を返す
* 関数はモナディック操作を使用して構築される
  （bind, `do`記法）

このような場合、Leanは関数を定義し、追加のヘルプなしで
方程式を証明することができます。

ユーザーは後で必要に応じて、関数が全体的であること
（つまり、`Option.none`を返さないこと）を証明できます。

この例についてのZulipでの詳細：
https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/McCarthy.2091.20function.20using.20partial_fixpoint
-/
