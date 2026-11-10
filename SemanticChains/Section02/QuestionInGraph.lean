import SemanticChains.Section01.QuestionAndRoot
import SemanticChains.Section02.ContractGraph

/-! §2.2. Представление вопроса в графе контракта.
Именование и подтверждённая отсылка дают один и тот же тип свидетельства.
Здесь фиксируется результат интерпретации вопроса в данном контракте. -/

namespace SemanticChains.Section02

open LemmaOne (State InQuestion FullAnswer Sufficient)

variable {T : State} {Fact I : Type} {M : ChainModel T Fact I}

/-- Известный факт: в вопросе Q по адресу e предъявлено обозначение в
конкретной роли. Его интерпретация указывает на зарегистрированный факт f. -/
structure NamedFact (M : ChainModel T Fact I) (Q : String) (e : T.Occ) (f : Fact) where
  wording : String
  role : T.Role
  mentioned : M.questionFactMention Q e = some (wording, role)
  identified : M.graph.Represents f e wording

/-- Если установленное содержание упоминания имеется в реестре, вхождению
вопроса соответствует ровно одна вершина. -/
theorem unique_named_vertex {Q : String} {e : T.Occ} {v : String}
    {role : T.Role} {c : T.Content}
    (mentioned : M.questionFactMention Q e = some (v, role))
    (read : T.interpret e v = some c)
    (known : c ∈ M.registered.map M.factContent) :
    ∃ f, Nonempty (NamedFact M Q e f) ∧
      ∀ g, Nonempty (NamedFact M Q e g) → g = f := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp known
  have identified : M.graph.Represents f e v := ⟨hf, read⟩
  refine ⟨f, ⟨⟨v, role, mentioned, identified⟩⟩, ?_⟩
  rintro g ⟨other⟩
  have sameWording := congrArg Prod.fst (Option.some.inj (other.mentioned.symm.trans mentioned))
  exact same_vertex other.identified identified (congrArg (T.interpret e) sameWording)

/-- «Почему Дэвид ушёл?» / «Что произошло после его ухода?». Смена роли
известного события (следствие / предшествующее событие) совместима с
тождеством вершины: для него достаточно совпадения полного содержания. -/
theorem same_fact_across_questions {Q₁ Q₂ : String} {e₁ e₂ : T.Occ} {f g : Fact}
    (first : NamedFact M Q₁ e₁ f) (second : NamedFact M Q₂ e₂ g)
    (same : T.interpret e₁ first.wording = T.interpret e₂ second.wording) :
    f = g := same_vertex first.identified second.identified same

/-- Известный объект: сравниваются разрешение указания в вопросе и
проверяемое обозначение в зафиксированном представлении факта. -/
structure ObjectMatch (M : ChainModel T Fact I) (Q : String) (e : T.Occ) (f : Fact) where
  object : T.Obj
  role : T.Role
  mentioned : T.questionRole Q e = some role
  resolved : T.resolve e = some object
  address : T.Occ
  wording : String
  represented : M.graph.Represents f address wording
  designated : M.presentation.Designates ⟨address, wording, M.factContent f, represented.2⟩ object

/-- У одного указания объект один, даже когда совпадения найдены у разных фактов. -/
theorem same_object_at_matches {Q : String} {e : T.Occ} {f g : Fact}
    (left : ObjectMatch M Q e f) (right : ObjectMatch M Q e g) :
    left.object = right.object := Option.some.inj (left.resolved.symm.trans right.resolved)

/-- Интерпретация открытого требования, например «x имел доступ o». Даны
известный объект, искомая роль и само требование с условиями. Подстановка
x задаёт содержание утверждения. В данных нет выбранного x или факта-ответа.
reports отмечает вхождения, перечисленные именно для этого требования. -/
structure OpenSlot (M : ChainModel T Fact I) (Q : String) where
  known : T.Obj
  inQuestion : InQuestion T Q known
  soughtRole : T.Role
  request : T.Requirement
  asked : T.requests Q request
  claim : T.Obj → T.Obj → T.Content
  reports : T.Content → T.Occ → Prop
  /-- Что утверждает полный ответ о каждом названном участнике. -/
  meaning : ∀ {a e x}, T.supplies a request → reports a e →
    T.answerRole a e = some soughtRole → T.resolve e = some x → M.Entails a (claim known x)

/-- Значение переменной x прочитано в полном ответе в требуемой роли. -/
def OpenSlot.Returned {Q : String} (slot : OpenSlot M Q) (a : T.Content) (x : T.Obj) : Prop :=
  ∃ e, slot.reports a e ∧ T.answerRole a e = some slot.soughtRole ∧ T.resolve e = some x

/-- По К3 и К5 один и тот же выбранный набор фактов обосновывает q(x)
для каждого x, предъявленного в полном ответе. Ни один новый факт из
остального контракта при переходе к отдельному участнику не добавляется. -/
theorem returned_values_justified {Q A : String} {a : T.Content} (slot : OpenSlot M Q)
    (full : FullAnswer T Q A a)
    (sufficient : Sufficient (Section01.evidence M) (fun f => f ∈ M.registered) a) :
    ∃ selected : List Fact, (∀ f ∈ selected, f ∈ M.registered) ∧
      ∀ x, slot.Returned a x → ∀ i,
        (∀ f ∈ selected, M.holds (M.factContent f) i) → M.holds (slot.claim slot.known x) i := by
  obtain ⟨selected, registered, enough⟩ := sufficient
  refine ⟨selected, registered, ?_⟩
  rintro x ⟨e, reported, role, resolves⟩ i premises
  exact slot.meaning (full.complete slot.request slot.asked) reported role resolves i (enough i premises)

#print axioms unique_named_vertex
#print axioms same_fact_across_questions
#print axioms same_object_at_matches
#print axioms returned_values_justified

end SemanticChains.Section02
