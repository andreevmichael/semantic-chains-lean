import SemanticChains.Section03.ContractSearch

/-! §3.2. Начальные факты в одном фиксированном состоянии T.
I_T(o) уже задано объектным запросом §3.1. Для I_T(Q) перебираются факты T:
достаточно одного совпадения с объектом вопроса до раскрытия рёбер.
Те же определения относятся к Tₜ после регистрации выведенных фактов. -/

namespace SemanticChains.Section03

open LemmaOne (State Anchored InQuestion)

variable {T : State} {Fact I : Type} (M : ChainModel T Fact I)

/-- Нужная для данного Q часть Т11. Существование записи задаётся условием
модели, а её попадание в результат доказывается по правилам запроса. -/
def QuestionObjectsCovered (Q : String) : Prop :=
  ∀ o, InQuestion T Q o → ∃ f, M.graph.RecordedObject f o

noncomputable def initialFacts (Q : String) : List Fact :=
  lookup M fun f => ∃ o, InQuestion T Q o ∧ M.graph.RecordedObject f o

/-- I_T(Q) есть объединение I_T(o) по всем объектам вопроса. -/
theorem mem_initialFacts {Q : String} {f : Fact} :
    f ∈ initialFacts M Q ↔ ∃ o, InQuestion T Q o ∧ f ∈ run M (.object o) := by
  unfold initialFacts
  rw [mem_lookup]
  constructor
  · rintro ⟨registered, o, inQ, recorded⟩
    exact ⟨o, inQ, (mem_run M _ _).2 ⟨registered, recorded⟩⟩
  · rintro ⟨o, inQ, hit⟩
    obtain ⟨registered, recorded⟩ := (mem_run M _ _).1 hit
    exact ⟨registered, o, inQ, recorded⟩

/-- Применимо, в частности, к носителю Fₒ из формулировки теоремы.
Не нужны ни его принадлежность S, ни обозначение o в ответе. -/
theorem recorded_fact_is_initial {Q : String} {o : T.Obj} {f : Fact}
    (inQ : InQuestion T Q o) (recorded : M.graph.RecordedObject f o) :
    f ∈ initialFacts M Q := by
  obtain ⟨addr, v, reading, designation⟩ := recorded
  apply (mem_initialFacts M).2
  exact ⟨o, inQ, (mem_run M _ _).2 ⟨reading.1, addr, v, reading, designation⟩⟩

/-- К1.1 даёт исходный объект; Т11 — факт с подтверждённым обозначением;
§3.1 обеспечивает обнаружение факта. -/
theorem initialFacts_nonempty {Q : String} (anchored : Anchored T Q)
    (covered : QuestionObjectsCovered M Q) : ∃ f, f ∈ initialFacts M Q := by
  obtain ⟨e, role, o, atQuestion, resolved⟩ := anchored
  have inQ : InQuestion T Q o := ⟨e, role, atQuestion, resolved⟩
  obtain ⟨f, recorded⟩ := covered o inQ
  exact ⟨f, recorded_fact_is_initial M inQ recorded⟩

/-- Один факт с несколькими совпадениями встречается один раз. Число
различных начальных фактов не превосходит длины исходного реестра. -/
theorem initialFacts_finite (Q : String) :
    (initialFacts M Q).Nodup ∧ (initialFacts M Q).length ≤ M.registered.length :=
  ⟨nodup_lookup M _, length_lookup_le M _⟩

#print axioms mem_initialFacts
#print axioms initialFacts_nonempty
#print axioms initialFacts_finite

end SemanticChains.Section03
