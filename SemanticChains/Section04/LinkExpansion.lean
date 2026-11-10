import SemanticChains.Section04.ChainExistence

/-! §4.3. Замена одного звена упорядоченным блоком вложенных фактов. -/
namespace SemanticChains.Section04

open LemmaOne (State InQuestion InFullAnswer)

variable {T : State} {Fact I : Type} {M : ChainModel T Fact I} {E : Expansion M}

def neighborPairs {α : Type} (xs : List α) := xs.zip xs.tail

private theorem adjacent_iff_pairs {α : Type} (rel : α → α → Prop) (xs : List α) :
    ChainModel.adjacent rel xs ↔ ∀ pair ∈ neighborPairs xs, rel pair.1 pair.2 := by
  match xs with
  | [] | [_] => simp [ChainModel.adjacent, neighborPairs]
  | x :: y :: ys =>
    rw [ChainModel.adjacent, adjacent_iff_pairs rel (y :: ys)]
    simp [neighborPairs, List.zip_cons_cons]

/-- Для фиксированных текстов можно собрать список ключей, выбирая один
общий объект на каждой границе. Порядок предикатов совпадает с порядком текстов. -/
private theorem exists_keys_iff (xs : List (T.Obj → Prop)) (nonempty : xs ≠ []) :
    (∃ keys, ChainModel.keyed (T := T) xs keys) ↔
      ∀ pair ∈ neighborPairs xs, ∃ o, pair.1 o ∧ pair.2 o := by
  match xs with
  | [] => exact False.elim (nonempty rfl)
  | [_] => exact ⟨fun _ => by simp [neighborPairs], fun _ => ⟨[], trivial⟩⟩
  | x :: y :: ys =>
    have tail := exists_keys_iff (y :: ys) (by simp)
    change (∃ keys, ChainModel.keyed (T := T) (x :: y :: ys) keys) ↔
      ∀ pair ∈ (x, y) :: neighborPairs (y :: ys), ∃ o, pair.1 o ∧ pair.2 o
    rw [List.forall_mem_cons]
    constructor
    · rintro ⟨keys, keyed⟩
      cases keys with
      | nil => contradiction
      | cons o rest => exact ⟨⟨o, keyed.1, keyed.2.1⟩, tail.1 ⟨rest, keyed.2.2⟩⟩
    · rintro ⟨⟨o, left, right⟩, others⟩
      obtain ⟨rest, keyed⟩ := tail.2 others
      exact ⟨o :: rest, left, right, keyed⟩

/-- Ранее проверенная пара остаётся пригодной. Для всех остальных пар
новой последовательности нужно предъявить новое свидетельство. -/
def NewNeighbors {α : Type} (rel : α → α → Prop) (before after : List α) : Prop :=
  ∀ pair ∈ neighborPairs after, pair ∉ neighborPairs before → rel pair.1 pair.2

private theorem reuse_neighbors {α : Type} {rel : α → α → Prop} {before after : List α}
    (old : ∀ pair ∈ neighborPairs before, rel pair.1 pair.2)
    (fresh : NewNeighbors rel before after) : ∀ pair ∈ neighborPairs after, rel pair.1 pair.2 := by
  intro pair h
  by_cases known : pair ∈ neighborPairs before
  · exact old pair known
  · exact fresh pair h known

/-- Границы включают вопрос и полный ответ. Каждый текст задаёт один
предикат обозначения, общий для входящего и исходящего переходов. -/
def boundaries (M : ChainModel T Fact I) (Q : String) (a : T.Content) (links : List (Link T Fact)) :=
  InQuestion T Q :: links.map (fun l => M.presentation.Designates l.2) ++ [InFullAnswer T a]

/-- Условия одной замены. Исходная цепочка уже проверена. Тексты вне
блока сохраняются, а вклад и обоснование проверяются во всём новом порядке. -/
structure ReplacementChecks (E : Expansion M) (Q : String) (a : T.Content)
    (pre : List (Link T Fact)) (parent : Link T Fact) (post block : List (Link T Fact)) (o : T.Obj) : Prop where
  nonempty : block ≠ []
  nested : ∀ l ∈ block, l.1 ≠ parent.1 ∧ Nonempty (Path E.Edge parent.1 l.1)
  distinct : ((pre ++ block ++ post).map Prod.fst).Nodup
  structural : NewNeighbors E.Connected ((pre ++ parent :: post).map Prod.fst)
    ((pre ++ block ++ post).map Prod.fst)
  lexicalKeys : NewNeighbors (fun left right => ∃ k, left k ∧ right k)
    (boundaries M Q a (pre ++ parent :: post)) (boundaries M Q a (pre ++ block ++ post))
  contributes : ∀ left l right, pre ++ block ++ post = left ++ l :: right →
    M.contributes Q a left l right
  enough : ∀ i, (∀ l ∈ pre ++ block ++ post, M.holds (l.2.textContent) i) → M.holds a i
  common : InQuestion T Q o ∧ InFullAnswer T a o ∧
    ∃ l ∈ pre ++ block ++ post, M.presentation.Designates l.2 o

theorem replacement_supports_now {Q : String} {a : T.Content} {pre post block : List (Link T Fact)}
    {parent : Link T Fact} {oldKeys : List T.Obj} {oldObject o : T.Obj}
    (old : M.SupportsNow E Q a (pre ++ parent :: post) oldKeys oldObject)
    (check : ReplacementChecks E Q a pre parent post block o) :
    ∃ keys, M.SupportsNow E Q a (pre ++ block ++ post) keys o := by
  obtain ⟨_, _, represented, _, _, structureOld, lexicalOld, _⟩ := old
  have parentInS := represented parent (by simp)
  have pairs := reuse_neighbors ((adjacent_iff_pairs _ _).1 structureOld) check.structural
  have boundaryPairs := (exists_keys_iff (T := T) (boundaries M Q a (pre ++ parent :: post))
    (by simp [boundaries])).1 ⟨oldKeys, lexicalOld⟩
  obtain ⟨keys, keyed⟩ := (exists_keys_iff (T := T) (boundaries M Q a (pre ++ block ++ post))
    (by simp [boundaries])).2 (reuse_neighbors boundaryPairs check.lexicalKeys)
  refine ⟨keys, by simp [check.nonempty], check.distinct, ?_, check.contributes, check.enough,
    (adjacent_iff_pairs _ _).2 pairs, keyed, check.common⟩
  intro l hl
  rcases List.mem_append.mp hl with left | right
  · rcases List.mem_append.mp left with prev | inserted
    · exact represented l (List.mem_append_left _ prev)
    · obtain ⟨toParent⟩ := parentInS
      obtain ⟨toChild⟩ := (check.nested l inserted).2
      exact ⟨toParent.append toChild⟩
  · exact represented l (List.mem_append_right _ (List.mem_cons_of_mem _ right))

/-- Для принятия нового блока проверяем также происхождение его текстов
по П3 при конкретных ключах этой замены. -/
theorem replacement_supports {Q : String} {a : T.Content} {pre post block : List (Link T Fact)}
    {parent : Link T Fact} {oldKeys keys : List T.Obj} {oldObject o : T.Obj}
    (old : M.Supports E Q a (pre ++ parent :: post) oldKeys oldObject)
    (check : ReplacementChecks E Q a pre parent post block o)
    (boundary : ChainModel.keyed (boundaries M Q a (pre ++ block ++ post)) keys)
    (origin : M.HasOrigin E Q a (pre ++ block ++ post) keys o) :
    M.Supports E Q a (pre ++ block ++ post) keys o := by
  obtain ⟨_, nonempty, distinct, nodes, roles, enough, connected, _, common⟩ :=
    replacement_supports_now old.now check
  exact ChainModel.supports_iff_now_and_origin.mpr
    ⟨⟨nonempty, distinct, nodes, roles, enough, connected, boundary, common⟩, origin⟩

/-- Родитель остаётся вершиной S, а среди оснований нового порядка
его больше нет. Это верно и для замены в середине цепочки. -/
theorem expanded_parent {Q : String} {a : T.Content} {pre post block : List (Link T Fact)}
    {parent : Link T Fact} {keys : List T.Obj} {oldObject o : T.Obj}
    (old : M.SupportsNow E Q a (pre ++ parent :: post) keys oldObject)
    (check : ReplacementChecks E Q a pre parent post block o) :
    E.InS parent.1 ∧ parent.1 ∉ (pre ++ block ++ post).map Prod.fst := by
  obtain ⟨_, unique, represented, _⟩ := old
  refine ⟨represented parent (by simp), ?_⟩
  rw [List.map_append, List.map_cons, List.nodup_append] at unique
  simp only [List.map_append, List.mem_append]
  rintro ((left | inside) | right)
  · exact unique.2.2 _ left _ List.mem_cons_self rfl
  · obtain ⟨l, hl, eq⟩ := List.mem_map.mp inside
    exact (check.nested l hl).1 eq
  · exact (List.nodup_cons.mp unique.2.1).1 right

/-- Последовательность предложенных замен. На каждом шаге меняется одна
позиция. Контракт, граф S, вопрос и содержание ответа фиксированы. -/
inductive Replacements (E : Expansion M) (Q : String) (a : T.Content) :
    List (Link T Fact) → List (Link T Fact) → Prop where
  | done (links) : Replacements E Q a links links
  | step {start pre parent post block keys o} :
      Replacements E Q a start (pre ++ parent :: post) →
      ReplacementChecks E Q a pre parent post block o →
      ChainModel.keyed (boundaries M Q a (pre ++ block ++ post)) keys →
      M.HasOrigin E Q a (pre ++ block ++ post) keys o →
      Replacements E Q a start (pre ++ block ++ post)

/-- Любая конечная последовательность принятых замен сохраняет обоснование
того же полного ответа и даёт ключи для итогового порядка. -/
theorem replacements_preserve {Q : String} {a : T.Content} {start final : List (Link T Fact)}
    (steps : Replacements E Q a start final)
    (initial : ∃ o keys, M.Supports E Q a start keys o) :
    ∃ o keys, M.Supports E Q a final keys o := by
  induction steps with
  | done => exact initial
  | step previous check boundary origin ih =>
    obtain ⟨_, _, old⟩ := ih
    exact ⟨_, _, replacement_supports old check boundary origin⟩

/-- Перестановка тех же текстов сохраняет их совместное содержание.
Если при допустимой интерпретации они истинны, а требуемое отношение
ложно, никакой их порядок не обоснует этот ответ. -/
theorem missing_relation_in_any_order {Q : String} {a relation : T.Content}
    {texts ordered : List (Link T Fact)} (order : texts.Perm ordered)
    (required : M.Entails a relation)
    (counterexample : ∃ i, (∀ l ∈ texts, M.holds (l.2.textContent) i) ∧ ¬ M.holds relation i) :
    ∀ keys o, ¬ M.SupportsNow E Q a ordered keys o := by
  rintro keys o ⟨_, _, _, _, enough, _⟩
  obtain ⟨i, holds, missing⟩ := counterexample
  exact missing (required i (enough i (fun l hl => holds l (order.mem_iff.mpr hl))))

#print axioms expanded_parent
#print axioms replacement_supports
#print axioms replacements_preserve
#print axioms missing_relation_in_any_order

end SemanticChains.Section04
