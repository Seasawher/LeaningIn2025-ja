/--
ネストされた再帰（追加資料）
=================================

次のデータ構造を考えてみましょう：
ノードが値と子のリストを持つツリー。
-/

structure Tree (α : Type) where
  val : α
  children : List (Tree α)

/-
このようなツリーに対して`map`関数が欲しいことがよくあります：
-/

def Tree.map (f : α → β) : Tree α → Tree β
  | ⟨val, children⟩ =>
    ⟨f val, List.map (fun t => Tree.map f t) children⟩
termination_by t => t
decreasing_by
  trace_state
  decreasing_tactic

/-
ここでは、Leanは`List.map`によって提供される`t`が
実際にリスト`children`のメンバーであることを知っています：
スコープ内に`t ∈ children`が入ります。
-/

/-
最近まで、Leanはこれを知りませんでした：
-/
set_option wf.preprocess false


/--
error: failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type
val : α
children : List (Tree α)
t : Tree α
⊢ sizeOf t < 1 + sizeOf children
-/
#guard_msgs in
def Tree.map' (f : α → β) : Tree α → Tree β
  | ⟨val, children⟩ =>
    ⟨f val, List.map (fun t => Tree.map' f t) children⟩
termination_by t => t

/--
これにはユーザーが必要な情報を注入するために`List.attach`を使用する必要がありました：
-/

def Tree.map'' (f : α → β) : Tree α → Tree β
  | ⟨val, children⟩ =>
    ⟨f val, List.map (fun ⟨t, _h⟩ => Tree.map'' f t) (List.attach children)⟩
termination_by t => t
