import SemanticChains.MainTheorem

/-! §1.1. Вопрос и верхнее основание ответа.
Все проверки относятся к одной интерпретации вопроса и одному состоянию
контракта. Для независимых вопросов по К1.2 проверка применяется к каждому
из них отдельно. -/

namespace SemanticChains.Section01

open LemmaOne (State FullAnswer Evidence Sufficient)

variable {T : State} {Fact I : Type} {M : ChainModel T Fact I}

/-- Содержания фактов интерпретируются в тех же условиях, что и полный ответ. -/
def evidence (M : ChainModel T Fact I) : Evidence T.Content Fact I where
  holds f := M.holds (M.factContent f)
  means := M.holds

/-- Утверждение 1.1. Проверенный факт r может служить основанием данного
ответа. Свидетелем достаточности по К5 служит ровно список [r].
К3 продолжает действовать для всех требований, включая условия вопроса. -/
theorem proposition_1_1 {Q A : String} {a : T.Content} {r : Fact}
    (full : FullAnswer T Q A a) (registered : r ∈ M.registered)
    (expresses : M.expresses Q a r) (justifies : M.Entails (M.factContent r) a) :
    M.PossibleRoot Q a r ∧ (∀ req, T.requests Q req → T.supplies a req) ∧
      Sufficient (evidence M) (fun f => f ∈ M.registered) a := by
  refine ⟨⟨registered, expresses, justifies⟩, full.complete, [r], ?_, ?_⟩
  · intro f hf
    have eq : f = r := List.mem_singleton.mp hf
    exact eq ▸ registered
  · intro i satisfies
    exact justifies i (satisfies r (List.mem_singleton.mpr rfl))

/-- Любое полное предъявление проверенного основания выражает его содержание.
Смена словесной формы сохраняет обоснование ответа и вклад этого факта. -/
theorem full_text_of_root {Q : String} {a : T.Content} {r : Fact} {v : Reading T}
    (root : M.PossibleRoot Q a r) (full : M.presentation.Full r v) :
    M.Entails (v.textContent) a ∧ M.contributes Q a [] (r, v) [] := by
  exact ⟨M.full_content full ▸ root.justifies, M.full_contributes root.expresses full⟩

/-- Если выбранные непосредственные подфакты совместно обосновывают Â, их
полные тексты также дают достаточное предъявление. Состав S сохраняется:
родитель принадлежит ему по пути длины ноль, дети — по выбранным вхождениям.
Здесь ещё не проверяется порядок звеньев цепочки (§4). -/
theorem present_by_subfacts {E : Expansion M} {a : T.Content}
    (texts : List (Link T Fact))
    (children : ∀ l ∈ texts, Nonempty (E.Edge E.root l.1))
    (full : ∀ l ∈ texts, M.presentation.Full l.1 l.2)
    (enough : ∀ i, (∀ l ∈ texts, M.holds (M.factContent l.1) i) → M.holds a i) :
    E.InS E.root ∧ (∀ l ∈ texts, E.InS l.1) ∧
      ∀ i, (∀ l ∈ texts, M.holds (l.2.textContent) i) → M.holds a i := by
  refine ⟨⟨.here E.root⟩, ?_, ?_⟩
  · intro l hl
    obtain ⟨w⟩ := children l hl
    exact ⟨.step w (.here l.1)⟩
  · intro i h
    apply enough i
    intro l hl
    rw [← M.full_content (full l hl)]
    exact h l hl

/-- Если при некотором допустимом истолковании все выбранные подфакты
истинны, но требуемое отношение не установлено (здесь ложно), одних подфактов
для полного ответа недостаточно. Свидетель различия должен быть предъявлен. -/
theorem missing_relation {a relation : T.Content} {children : List Fact}
    (required : M.Entails a relation)
    (witness : ∃ i, (∀ f ∈ children, M.holds (M.factContent f) i) ∧ ¬ M.holds relation i) :
    ¬ (∀ i, (∀ f ∈ children, M.holds (M.factContent f) i) → M.holds a i) := by
  obtain ⟨i, facts, missing⟩ := witness
  exact fun enough => missing (required i (enough i facts))

#print axioms proposition_1_1
#print axioms full_text_of_root
#print axioms present_by_subfacts
#print axioms missing_relation

end SemanticChains.Section01
