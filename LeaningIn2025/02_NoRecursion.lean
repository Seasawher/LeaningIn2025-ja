/-
Leanには再帰的定義がない
================================

Leanで実装されているロジックは再帰をサポートしていません。
カーネルは再帰的定義を拒否します。

それでも再帰的定義を試してみましょう…
（これはLeanの正しい使い方ではありません）

-/

import Lean

open Lean Meta Elab Term

-- def test := fun (n : Nat) => test (n + 1)

/--
info: value: fun n => test (n + 1)
---
error: (kernel) unknown constant 'test'
-/
#guard_msgs in
run_elab
  let name := `test
  let type ← elabTerm (← `(Nat → Nat)) none
  let value ← withLocalDeclD `n (mkConst `Nat) fun n =>
    mkLambdaFVars #[n] <|
      mkApp (mkConst `test)
            (mkNatAdd n (mkNatLit 1))
  logInfo m!"value: {value}"
  Lean.addDecl (.defnDecl {
    name, type, value, levelParams := []
    hints := .regular 0, safety := .safe
  })

/-
健全性
---------

なぜLeanのカーネルが他のプログラミング言語のように
単純に再帰的定義を受け入れないことがそれほど重要なのでしょうか？

それはすぐにロジックの健全性を破壊するからです；
このようにどんな命題でも証明できてしまいます：
```
def reallyBad {P : Prop} : P := reallyBad
```
-/
