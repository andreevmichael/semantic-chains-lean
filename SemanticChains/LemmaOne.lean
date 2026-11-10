/-! Лемма 1. Общий лексический ключ вопроса и полного ответа (К1.1, К3–К6).
Один State фиксирует контракт, включая проверенные основания разрешения отсылок.
Occ — конкретное вхождение по адресу; Content — полное содержание, которое могут
предъявлять разные строки. Графы и цепочки в этой лемме не участвуют. -/

namespace SemanticChains.LemmaOne

structure State where
  Obj : Type
  Occ : Type
  Role : Type
  Content : Type
  /-- Установленное чтение конкретного предъявления в фиксированном контракте. -/
  interpret : Occ → String → Option Content
  Requirement : Type
  /-- Роль указанного в вопросе объекта, если вхождение принадлежит вопросу. -/
  questionRole : String → Occ → Option Role
  /-- Роль вхождения в восстановленном полном содержании. -/
  answerRole : Content → Occ → Option Role
  /-- some o означает проверенное в данном контракте однозначное разрешение. -/
  resolve : Occ → Option Obj
  requests : String → Requirement → Prop
  supplies : Content → Requirement → Prop
  /-- Восстановление по вопросу и исходному (возможно, краткому) ответу. -/
  recovers : String → String → Content → Prop

/-- К1.1: вопрос указывает хотя бы на один разрешимый объект в некоторой роли. -/
def Anchored (T : State) (Q : String) : Prop :=
  ∃ e role o, T.questionRole Q e = some role ∧ T.resolve e = some o

/-- К3–К4. Требования включают условия вопроса. Единственность относится
к полному содержанию, а не к его словесному представлению. -/
structure FullAnswer (T : State) (Q A : String) (full : T.Content) : Prop where
  recovered : T.recovers Q A full
  uniqueContent : ∀ other, T.recovers Q A other → other = full
  complete : ∀ req, T.requests Q req → T.supplies full req
  preserves : ∀ e role o, T.questionRole Q e = some role → T.resolve e = some o →
    ∃ e', T.answerRole full e' = some role ∧ T.resolve e' = some o

def InQuestion (T : State) (Q : String) (o : T.Obj) : Prop :=
  ∃ e role, T.questionRole Q e = some role ∧ T.resolve e = some o

def InFullAnswer (T : State) (full : T.Content) (o : T.Obj) : Prop :=
  ∃ e role, T.answerRole full e = some role ∧ T.resolve e = some o

/-- Оба вхождения и их разрешение в одном состоянии. -/
structure LexicalKey (T : State) (Q : String) (full : T.Content) where
  object : T.Obj
  role : T.Role
  questionOccurrence : T.Occ
  answerOccurrence : T.Occ
  atQuestion : T.questionRole Q questionOccurrence = some role
  atAnswer : T.answerRole full answerOccurrence = some role
  fromQuestion : T.resolve questionOccurrence = some object
  fromAnswer : T.resolve answerOccurrence = some object

/-- Лексическая часть леммы. recovered — любое содержание, полученное при
восстановлении краткого A. К4 отождествляет его с полным содержанием,
для которого установлены свойства К3. -/
theorem common_lexical_key {T : State} {Q A : String} {full recovered : T.Content}
    (question : Anchored T Q) (answer : FullAnswer T Q A full)
    (restored : T.recovers Q A recovered) : Nonempty (LexicalKey T Q recovered) := by
  obtain ⟨q, role, o, hq, rq⟩ := question
  obtain ⟨a, ha, ra⟩ := answer.preserves q role o hq rq
  obtain rfl := answer.uniqueContent recovered restored
  exact ⟨⟨o, role, q, a, hq, ha, rq, ra⟩⟩

theorem common_object {T : State} {Q A : String} {full : T.Content}
    (question : Anchored T Q) (answer : FullAnswer T Q A full) :
    ∃ o, InQuestion T Q o ∧ InFullAnswer T full o := by
  obtain ⟨k⟩ := common_lexical_key question answer answer.recovered
  exact ⟨k.object, ⟨k.questionOccurrence, k.role, k.atQuestion, k.fromQuestion⟩,
    ⟨k.answerOccurrence, k.role, k.atAnswer, k.fromAnswer⟩⟩

#print axioms common_lexical_key
#print axioms common_object

/-- К5. Обоснование проверяется только на выбранных доступных фактах.
Все интерпретации имеют фиксированные значения обозначений. -/
structure Evidence (Content Fact I : Type) where
  holds : Fact → I → Prop
  means : Content → I → Prop

def Sufficient {Content Fact I : Type} (E : Evidence Content Fact I)
    (available : Fact → Prop) (full : Content) : Prop :=
  ∃ selected : List Fact, (∀ f ∈ selected, available f) ∧
    ∀ i, (∀ f ∈ selected, E.holds f i) → E.means full i

/-- К6: каждый новый факт сохраняет проверенное основание вывода —
список доступных посылок и применимое корректное правило. -/
inductive Extensions {Content Fact I Rule : Type} (E : Evidence Content Fact I)
    (applies : Rule → List Fact → Fact → Prop) (initial : Fact → Prop) :
    (Fact → Prop) → Type where
  | start : Extensions E applies initial initial
  | add {available : Fact → Prop} (previous : Extensions E applies initial available)
      {d : Fact} (fresh : ¬ available d) (premises : List Fact) (rule : Rule)
      (present : ∀ f ∈ premises, available f) (valid : applies rule premises d) :
      Extensions E applies initial (fun f => available f ∨ f = d)

/-- Подстановка обоснований посылок на каждом шаге расширения, лемма 1 (*). -/
theorem grounded_extension {Content Fact I Rule : Type} {E : Evidence Content Fact I}
    {applies : Rule → List Fact → Fact → Prop} {initial available : Fact → Prop}
    (sound : ∀ rule ps d, applies rule ps d →
      ∀ i, (∀ f ∈ ps, E.holds f i) → E.holds d i)
    (steps : Extensions E applies initial available) :
    ∀ i, (∀ f, initial f → E.holds f i) → ∀ f, available f → E.holds f i := by
  induction steps with
  | start => exact fun _ h => h
  | add previous fresh ps rule present valid ih =>
    intro i h f hf
    rcases hf with earlier | rfl
    · exact ih i h f earlier
    · exact sound rule ps _ valid i (fun g hg => ih i h g (present g hg))

/-- Общий ключ в выбранном состоянии и обоснование ответа через исходный
контракт. Для T₀ берём start. Для Tₜ К1.1, К3 и К4 должны выполняться в Tₜ;
их сохранение при изменении интерпретации обозначений не предполагается. -/
theorem grounded_key {T : State} {Q A : String} {full : T.Content}
    {Fact I Rule : Type} {E : Evidence T.Content Fact I}
    {applies : Rule → List Fact → Fact → Prop} {initial available : Fact → Prop}
    (question : Anchored T Q) (answer : FullAnswer T Q A full)
    (enough : Sufficient E available full)
    (sound : ∀ rule ps d, applies rule ps d →
      ∀ i, (∀ f ∈ ps, E.holds f i) → E.holds d i)
    (steps : Extensions E applies initial available) :
    Nonempty (LexicalKey T Q full) ∧
      ∀ i, (∀ f, initial f → E.holds f i) → E.means full i := by
  refine ⟨common_lexical_key question answer answer.recovered, ?_⟩
  obtain ⟨selected, present, entails⟩ := enough
  intro i h
  exact entails i (fun f hf => grounded_extension sound steps i h f (present f hf))

#print axioms grounded_extension
#print axioms grounded_key

end SemanticChains.LemmaOne
