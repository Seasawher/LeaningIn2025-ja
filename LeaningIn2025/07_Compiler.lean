/-!

コンパイラ vs. カーネル
===================

これまでは定理証明器としてのLeanについてのみ話し、
カーネルが受け入れる形式に再帰的定義を取り込む
さまざまな方法について説明しました。

Leanはプログラミング言語でもあり、ネイティブコードに
コンパイルすることができます。コンパイラは以下の場合に使用されます：
* プログラムのコンパイル（当然）
* 式を評価するための`#eval`の使用
* 証明での`by native_decide`の使用。

コンパイラは再帰をサポートし、構造的/整礎帰納法/部分固定点の
機構が適用される前の定義を確認します。コンパイラにとって、
以下は同一です：
-/

def add₁ : (a b : Nat) → Option Nat
| .zero, b => b
| .succ a', b => Nat.succ <$> add₁ a' b
termination_by structural a => a -- 明示的に構造的再帰を使用

def add₂ : (a b : Nat) → Option Nat
| .zero, b => b
| .succ a', b => Nat.succ <$> add₂ a' b
termination_by a => a -- 整礎帰納法による再帰

def add₃ : (a b : Nat) → Option Nat
| .zero, b => b
| .succ a', b => Nat.succ <$> add₃ a' b
partial_fixpoint

/-
カーネルを無視する
-------------------

定義に対して証明を行う予定がない場合に役立つ
2つのバリアントがあります。

`partial`
---------

* 関数は無制限の再帰を使用できる
* 定義はカーネルに存在するが、完全に不透明
* 型は先験的に有効でなければならない
* `partial`は*感染性がない*

「通常の」プログラムでよく使用されます（Leanコードはこれでいっぱいです）
-/

partial def add₄ : (a b : Nat) → Option Nat
| .zero, b => b
| .succ a', b => Nat.succ <$> add₄ a' b

/--
`unsafe`
--------

* 関数は無制限の再帰を使用できる
* 他の`unsafe`機能も利用可能
* 定義はカーネルに表示されない
* `unsafe`は*感染性がある*
  （ただし、`implemented_by`を使用する場合は感染しません）。
-/

unsafe def add₅ : (a b : Nat) → Option Nat
| .zero, b => b
| .succ a', b => Nat.succ <$> add₅ a' b
