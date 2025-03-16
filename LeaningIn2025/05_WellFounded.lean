/-!
整礎帰納法による再帰
======================

構造的再帰ではない再帰関数を定義したい場合があります。

`Array`のすべての要素が同じかどうかを確認する
次の関数を考えてみましょう：
-/

def areAllSame (arr : Array Nat) (i : Nat) :=
  if _ : i < arr.size then
    if arr[i] = arr[0] then
      areAllSame arr (i + 1)
    else
      false
  else
    true
termination_by arr.size - i
decreasing_by
  omega

/-
これは構造的再帰ではありません（進むにつれて`i`が大きくなります）。

しかし、*減少測度*が存在します：
再帰呼び出しでは式`arr.size - i`が小さくなります。
測度は`termination_by`節で指定します。

これを通過させるためには、測度が減少することをLeanに証明する必要があります。
これは`decreasing_by`節で行われます。
-/

/-
自動再帰証明
--------------------------

多くの場合、Leanは終了測度や終了証明を自動的に推論します。
-/

def areAllSame' (arr : Array Nat) (i : Nat) :=
  if _ : i < arr.size then
    if arr[i] = arr[0] then
      areAllSame' arr (i + 1)
    else
      false
  else
    true

/-
終了測度を調査するには`termination_by?`を使用します。
-/

/-
辞書式順序
-------------------
終了測度はより複雑になる場合があります。例えば
「`a`が小さくなるか、`a`が同じままで`b`が小さくなる」というようなものです。

古典的な例：アッカーマン関数。
-/

def ackermann : (a b : Nat) → Nat
  | 0, b => b + 1
  | a + 1, 0 => ackermann a 1
  | a + 1, b + 1 => ackermann a (ackermann (a + 1) b)
-- termination_by?

/-
整礎帰納法による再帰の欠点
---------------------------------

整礎帰納法による再帰は（ほとんどの場合）構造的再帰よりも
厳密に強力です。では、なぜ構造的再帰を使うのでしょうか？

1. 明示的な証明が不要

2. カーネルの還元動作が良好。
   これは以下の点で重要です：
    * 型の定義
    * カーネル計算
      （例：`rfl`や`by decide`を使用した評価）。
-/
