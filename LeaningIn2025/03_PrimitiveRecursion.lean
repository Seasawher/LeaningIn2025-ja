/-!

原始的再帰
===================

では再帰をどのように表現するのでしょうか？

*再帰子*を使います。すべての帰納的データに対して、
原始的再帰的定義を定義するために使用できる再帰子が存在します。
-/

-- 自然数は帰納的定義です：

namespace JustToRecall

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

end JustToRecall

-- これが自然数の再帰子です：

/--
info: Nat.rec.{u}
  {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) : motive t
-/
#guard_msgs (whitespace := lax) in
#check Nat.rec
-- #print Nat.rec

/-
自然数の加算、通常の方法：

```
def add (a b : Nat) : Nat :=
  match a with
  | .zero => b
  | .succ a' => Nat.succ (add a' b)
```

再帰子を使用すると、再帰なしで定義できます：
-/

def add (a b : Nat) :=
  Nat.rec (motive := fun _ => Nat)
    (zero := b)
    (succ := fun _a' add_a'_b => Nat.succ add_a'_b)
    a

/-
そして、正常に動作します！
-/

/-- info: 35 -/
#guard_msgs in
#reduce add 12 23
