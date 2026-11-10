import SemanticChains.Section03.InitialFacts

/-! §3.3. Подъём от начальных фактов по сохраняющим рёбрам контракта. -/

namespace SemanticChains

def Path.length {Fact : Type} {R : Fact → Fact → Type} {p f : Fact} :
    Path R p f → Nat
  | .here _ => 0
  | .step _ tail => tail.length + 1

namespace Section03

open LemmaOne (State InQuestion)

variable {T : State} {Fact I : Type} (M : ChainModel T Fact I)

/-- Сохраняем найденные факты и добавляем родителей каждого из них.
Запрос работает во всём фиксированном контракте. -/
noncomputable def ascentStep (found : List Fact) : List Fact :=
  lookup M fun p => p ∈ found ∨ ∃ f ∈ found, p ∈ run M (.parents f)

noncomputable def ascent (Q : String) : Nat → List Fact
  | 0 => initialFacts M Q
  | n + 1 => ascentStep M (ascent Q n)

private theorem ascent_registered {Q : String} {n : Nat} {p : Fact}
    (hit : p ∈ ascent M Q n) : p ∈ M.registered := by
  cases n with
  | zero => exact ((mem_lookup M _ p).1 hit).1
  | succ n => exact ((mem_lookup M _ p).1 hit).1

theorem mem_ascent_succ {Q : String} {n : Nat} {p : Fact} :
    p ∈ ascent M Q (n + 1) ↔
      p ∈ ascent M Q n ∨ ∃ f ∈ ascent M Q n, Nonempty (M.graph.Edge p f) := by
  constructor
  · intro hit
    rcases ((mem_lookup M _ p).1 hit).2 with prev | ⟨f, prev, parent⟩
    · exact Or.inl prev
    · exact Or.inr ⟨f, prev, ((mem_run M _ p).1 parent).2⟩
  · rintro (prev | ⟨f, prev, ⟨edge⟩⟩)
    · exact (mem_lookup M _ p).2 ⟨ascent_registered M prev, Or.inl prev⟩
    · have parent := (mem_run M (.parents f) p).2 ⟨edge.property.1, ⟨edge⟩⟩
      exact (mem_lookup M _ p).2 ⟨edge.property.1, Or.inr ⟨f, prev, parent⟩⟩

/-- Лемма 3.3.1, после n шагов. Длина пути считается от родителя к
начальному факту, а поиск проходит те же рёбра в обратном направлении. -/
theorem mem_ascent_iff {Q : String} (n : Nat) (p : Fact) :
    p ∈ ascent M Q n ↔ ∃ f ∈ initialFacts M Q,
      ∃ path : Path M.graph.Edge p f, path.length ≤ n := by
  induction n generalizing p with
  | zero =>
    constructor
    · intro seed
      exact ⟨p, seed, .here p, Nat.le_refl 0⟩
    · rintro ⟨f, seed, path, bound⟩
      cases path with
      | here => exact seed
      | step edge tail => simp [Path.length] at bound
  | succ n ih =>
    rw [mem_ascent_succ]
    constructor
    · rintro (prev | ⟨c, prev, ⟨edge⟩⟩)
      · obtain ⟨f, seed, path, bound⟩ := (ih p).1 prev
        exact ⟨f, seed, path, Nat.le_succ_of_le bound⟩
      · obtain ⟨f, seed, tail, bound⟩ := (ih c).1 prev
        exact ⟨f, seed, .step edge tail, Nat.succ_le_succ bound⟩
    · rintro ⟨f, seed, path, bound⟩
      cases path with
      | here => exact Or.inl ((ih _).2 ⟨_, seed, .here _, Nat.zero_le _⟩)
      | step edge tail =>
        exact Or.inr ⟨_, (ih _).2 ⟨_, seed, tail, Nat.le_of_succ_le_succ bound⟩, ⟨edge⟩⟩

/-- Для носителя Fₒ из выбранного раскрытия поиск достигает его основания. -/
theorem ascent_finds_root {Q : String} {E : Expansion M} {f : Fact} {o : T.Obj}
    (selected : E.InS f) (inQ : InQuestion T Q o) (recorded : M.graph.RecordedObject f o) :
    ∃ n, E.root ∈ ascent M Q n := by
  obtain ⟨selectedPath⟩ := selected
  let path := Section02.contractPath selectedPath
  exact ⟨path.length, (mem_ascent_iff M _ _).2
    ⟨f, recorded_fact_is_initial M inQ recorded, path, Nat.le_refl _⟩⟩

private theorem ascent_mono {Q : String} {n m : Nat} {p : Fact} (le : n ≤ m)
    (hit : p ∈ ascent M Q n) : p ∈ ascent M Q m := by
  induction le with
  | refl => exact hit
  | step _ ih => exact (mem_ascent_succ M).2 (Or.inl ih)

/-- Конечный реестр даёт общий номер шага для всех обнаружимых фактов. -/
theorem ascent_stabilizes (Q : String) :
    ∃ N, ∀ m ≥ N, ∀ p, p ∈ ascent M Q m ↔ p ∈ ascent M Q N := by
  obtain ⟨N, covered⟩ := finite_search_stage M (ascent M Q) (ascent_registered M) (ascent_mono M)
  exact ⟨N, fun m le p => ⟨fun hit => (covered p).1 ⟨m, hit⟩, ascent_mono M le⟩⟩

/-- Если очередной шаг ничего не добавил, поиск можно остановить. -/
theorem ascent_stop {Q : String} {n : Nat}
    (stable : ∀ p, p ∈ ascent M Q (n + 1) ↔ p ∈ ascent M Q n) (k : Nat) :
    ∀ p, p ∈ ascent M Q (n + k) ↔ p ∈ ascent M Q n := by
  induction k with
  | zero => exact fun _ => Iff.rfl
  | succ k ih =>
    intro p
    rw [Nat.add_succ, mem_ascent_succ]
    simp only [ih]
    exact (mem_ascent_succ M).symm.trans (stable p)

#print axioms mem_ascent_iff
#print axioms ascent_finds_root
#print axioms ascent_stabilizes
#print axioms ascent_stop

end Section03
end SemanticChains
