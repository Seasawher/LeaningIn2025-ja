/-!
構造的再帰
====================

再帰関数を定義するために再帰子を使用するのは面倒なので、
Leanがその作業をしてくれて、次のように再帰関数を定義できます：
-/

def add (a b : Nat) : Nat :=
  match a with
  | .zero => b
  | .succ a' => Nat.succ (add a' b)

/-
しかし裏側では、これは再帰子を使用した非再帰的な定義に変換されています！
-/

/-
コース・オブ・バリュー再帰
-------------------------

実際、Leanはより強力な変換を使用しています。これは
*コース・オブ・バリュー再帰*と呼ばれ、パラメータの（直接的でない）
部分式に対する再帰呼び出しを可能にします：

古典的な例：
-/

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | Nat.succ (Nat.succ n') =>
    fib n' + fib (Nat.succ n')

/-
退屈で挑戦が必要ですか？`Nat.rec`を使って`fib`を定義してみてください！
-/

/-
相互再帰
----------------

原始的再帰に対するもう一つの追加機能は相互再帰のサポートです：
-/

mutual
  def even : Nat → Bool
  | 0 => true
  | Nat.succ n => odd n

  def odd : Nat → Bool
  | 0 => false
  | Nat.succ n => even n
end
