import SemanticChains.Section03.Ascent
import SemanticChains.Section02.AnswerGraph

/-! §3.4. Выращивание дерева отношений в одном фиксированном контракте. -/

namespace SemanticChains.Section03

open LemmaOne (State InQuestion)

variable {T : State} {Fact I : Type} (M : ChainModel T Fact I)

/-- Переход при обходе. В каждой альтернативе хранится исходное
свидетельство ребра вместе с его направлением. -/
abbrev Move (x y : Fact) := Sum (M.graph.Edge x y) (M.graph.Edge y x)

/-- Маршрут от начального факта s. Последний переход открывает вершину y. -/
inductive Walk (s : Fact) : Fact → Type where
  | start : Walk s s
  | next {x y : Fact} : Walk s x → Move M x y → Walk s y

def Walk.length {s y : Fact} : Walk M s y → Nat
  | .start => 0
  | .next before _ => before.length + 1

/-- W₀ — зарегистрированные начальные факты. Для одного факта берём [f],
для вопроса — initialFacts M Q. Каждый шаг проверяет оба запроса §3.1. -/
noncomputable def growth (seeds : List Fact) : Nat → List Fact
  | 0 => lookup M fun f => f ∈ seeds
  | n + 1 =>
    let found := growth seeds n
    lookup M fun y => y ∈ found ∨ ∃ x ∈ found,
      y ∈ run M (.children x) ∨ y ∈ run M (.parents x)

private theorem growth_registered {seeds : List Fact} {n : Nat} {y : Fact}
    (hit : y ∈ growth M seeds n) : y ∈ M.registered := by
  cases n <;> exact ((mem_lookup M _ y).1 hit).1

theorem mem_growth_succ {seeds : List Fact} {n : Nat} {y : Fact} :
    y ∈ growth M seeds (n + 1) ↔ y ∈ growth M seeds n ∨
      ∃ x ∈ growth M seeds n, Nonempty (Move M x y) := by
  constructor
  · intro hit
    rcases ((mem_lookup M _ y).1 hit).2 with old | ⟨x, old, child | parent⟩
    · exact Or.inl old
    · obtain ⟨edge⟩ := ((mem_run M (.children x) y).1 child).2
      exact Or.inr ⟨x, old, ⟨.inl edge⟩⟩
    · obtain ⟨edge⟩ := ((mem_run M (.parents x) y).1 parent).2
      exact Or.inr ⟨x, old, ⟨.inr edge⟩⟩
  · rintro (old | ⟨x, old, ⟨edge | edge⟩⟩)
    · exact (mem_lookup M _ y).2 ⟨growth_registered M old, Or.inl old⟩
    · have hit := (mem_run M (.children x) y).2 ⟨edge.property.2.1, ⟨edge⟩⟩
      exact (mem_lookup M _ y).2 ⟨edge.property.2.1, Or.inr ⟨x, old, Or.inl hit⟩⟩
    · have hit := (mem_run M (.parents x) y).2 ⟨edge.property.1, ⟨edge⟩⟩
      exact (mem_lookup M _ y).2 ⟨edge.property.1, Or.inr ⟨x, old, Or.inr hit⟩⟩

/-- Утверждение 3.4 на шаге n, включая маршрут нулевой длины. -/
theorem mem_growth_iff (seeds : List Fact) (n : Nat) (y : Fact) :
    y ∈ growth M seeds n ↔ ∃ s ∈ seeds, s ∈ M.registered ∧
      ∃ walk : Walk M s y, walk.length ≤ n := by
  induction n generalizing y with
  | zero =>
    constructor
    · intro hit
      obtain ⟨reg, seed⟩ := (mem_lookup M _ y).1 hit
      exact ⟨y, seed, reg, .start, Nat.le_refl 0⟩
    · rintro ⟨s, seed, reg, walk, bound⟩
      cases walk with
      | start => exact (mem_lookup M _ _).2 ⟨reg, seed⟩
      | next before edge => simp [Walk.length] at bound
  | succ n ih =>
    rw [mem_growth_succ]
    constructor
    · rintro (old | ⟨x, old, ⟨edge⟩⟩)
      · obtain ⟨s, seed, reg, walk, bound⟩ := (ih y).1 old
        exact ⟨s, seed, reg, walk, Nat.le_succ_of_le bound⟩
      · obtain ⟨s, seed, reg, walk, bound⟩ := (ih x).1 old
        exact ⟨s, seed, reg, .next walk edge, Nat.succ_le_succ bound⟩
    · rintro ⟨s, seed, reg, walk, bound⟩
      cases walk with
      | start => exact Or.inl ((ih _).2 ⟨_, seed, reg, .start, Nat.zero_le _⟩)
      | next before edge => exact Or.inr ⟨_, (ih _).2
          ⟨s, seed, reg, before, Nat.le_of_succ_le_succ bound⟩, ⟨edge⟩⟩

/-- Все открытые факты. Ниже показано, что они уже найдены на одном
конечном шаге и образуют объединение компонент начальных фактов. -/
def InW (seeds : List Fact) (y : Fact) : Prop := ∃ n, y ∈ growth M seeds n

theorem growth_stabilizes (seeds : List Fact) :
    ∃ N, ∀ y, InW M seeds y ↔ y ∈ growth M seeds N := by
  apply finite_search_stage M _ (growth_registered M)
  intro n m p le hit
  induction le with
  | refl => exact hit
  | step _ ih => exact (mem_growth_succ M).2 (Or.inl ih)

theorem growth_stop {seeds : List Fact} {n : Nat}
    (stable : ∀ y, y ∈ growth M seeds (n + 1) ↔ y ∈ growth M seeds n) (k : Nat) :
    ∀ y, y ∈ growth M seeds (n + k) ↔ y ∈ growth M seeds n := by
  induction k with
  | zero => exact fun _ => Iff.rfl
  | succ k ih =>
    intro y
    rw [Nat.add_succ, mem_growth_succ]
    simp only [ih]
    exact (mem_growth_succ M).symm.trans (stable y)

theorem inW_iff (seeds : List Fact) (y : Fact) :
    InW M seeds y ↔ ∃ s ∈ seeds, s ∈ M.registered ∧ Nonempty (Walk M s y) := by
  constructor
  · rintro ⟨n, hit⟩
    obtain ⟨s, seed, reg, walk, _⟩ := (mem_growth_iff M _ _ _).1 hit
    exact ⟨s, seed, reg, ⟨walk⟩⟩
  · rintro ⟨s, seed, reg, ⟨walk⟩⟩
    exact ⟨walk.length, (mem_growth_iff M _ _ _).2 ⟨s, seed, reg, walk, Nat.le_refl _⟩⟩

/-- Открытие любого конца сохраняющего пути позволяет обнаружить второй. -/
theorem inW_along_path {seeds : List Fact} {p f : Fact} (path : Path M.graph.Edge p f) :
    InW M seeds p ↔ InW M seeds f := by
  induction path with
  | here => exact Iff.rfl
  | step edge tail ih =>
    apply Iff.trans _ ih
    constructor <;> rintro ⟨n, hit⟩
    · exact ⟨n + 1, (mem_growth_succ M).2 (Or.inr ⟨_, hit, ⟨.inl edge⟩⟩)⟩
    · exact ⟨n + 1, (mem_growth_succ M).2 (Or.inr ⟨_, hit, ⟨.inr edge⟩⟩)⟩

/-- Если открыт любой факт выбранного разбора, открываются основание
и все остальные факты S, включая факты на соседних ветвях. -/
theorem selected_subset_growth {E : Expansion M} {seeds : List Fact} {f : Fact}
    (selected : E.InS f) (found : InW M seeds f) :
    ∀ y, E.InS y → InW M seeds y := by
  obtain ⟨toSeed⟩ := selected
  have root := (inW_along_path M (Section02.contractPath toSeed)).2 found
  rintro y ⟨toY⟩
  exact (inW_along_path M (Section02.contractPath toY)).1 root

/-- S ⊆ W для поиска от объектов вопроса. Область строится до выбора
раскрытия, а попадание носителя в W₀ следует из §3.2. -/
theorem selected_subset_question_growth {E : Expansion M} {Q : String} {f : Fact} {o : T.Obj}
    (selected : E.InS f) (inQ : InQuestion T Q o) (recorded : M.graph.RecordedObject f o) :
    ∀ y, E.InS y → InW M (initialFacts M Q) y := by
  have seed := recorded_fact_is_initial M inQ recorded
  have reg := ((mem_lookup M _ f).1 seed).1
  exact selected_subset_growth M selected ⟨0, (mem_lookup M _ f).2 ⟨reg, seed⟩⟩

/-- Индуцированный граф W сохраняет каждое направленное свидетельство
контракта, у которого обнаружены оба конца. -/
abbrev FoundEdge (seeds : List Fact) (p c : Fact) :=
  {_w : M.graph.Edge p c // InW M seeds p ∧ InW M seeds c}

/-- Вложение выбранного ребра в граф на W сохраняет само свидетельство. -/
def selectedFoundEdge {E : Expansion M} {seeds : List Fact} {f p c : Fact}
    (selected : E.InS f) (found : InW M seeds f) (edge : E.AnswerEdge p c) :
    FoundEdge M seeds p c :=
  let covered := selected_subset_growth M selected found
  let ends := E.edge_endpoints edge
  ⟨E.toContractEdge edge, covered p ends.1, covered c ends.2⟩

/-- Различные верхние факты контракта не могут быть соседями через общего
сохраняющего предка (§3.4, рис. 3.3), даже если найдены в одной компоненте. -/
theorem distinct_tops_not_connected {E : Expansion M} {p q : Fact}
    (hp : M.graph.IsTop p) (hq : M.graph.IsTop q) (ne : p ≠ q) : ¬ E.Connected p q := by
  rintro ⟨r, _, left, right, _⟩
  have rp := Section02.path_to_top (Section02.contractPath left) hp
  have rq := Section02.path_to_top (Section02.contractPath right) hq
  exact ne (rp.symm.trans rq)

#print axioms mem_growth_iff
#print axioms growth_stabilizes
#print axioms selected_subset_question_growth
#print axioms distinct_tops_not_connected

end SemanticChains.Section03
