import SemanticChains.LemmaOne
import SemanticChains.Presentation

/-! §2.1. Сохраняющий граф одного фиксированного контракта. -/
namespace SemanticChains

/-- Проверенное чтение. Содержание определяется адресом и строкой в T. -/
structure Reading (T : LemmaOne.State) where
  address : T.Occ
  wording : String
  textContent : T.Content
  verified : T.interpret address wording = some textContent

theorem Reading.unique {T : LemmaOne.State} {v u : Reading T}
    (address : v.address = u.address) (wording : v.wording = u.wording) :
    v.textContent = u.textContent := by
  have h := v.verified
  rw [address, wording, u.verified] at h
  exact (Option.some.inj h).symm

inductive OccurrenceKind where
  | inclusion
  | reference
  deriving DecidableEq

/-- Адрес конкретного вхождения в полном тексте родителя. -/
structure OccurrenceRecord (T : LemmaOne.State) where
  parentText : Reading T
  address : T.Occ
  role : T.Role
  kind : OccurrenceKind

/-- Данные принятого разбора. Тождество и полное сохранение относятся к
утверждённому содержанию с ролями, условиями и областью их действия.
readAt может разрешить и простую ссылку; ребру дополнительно нужно
свидетельство Occurrence с законами сохранения и раскрытия П2. -/
structure ContractGraph {Fact : Type} (T : LemmaOne.State)
    (P : Presentation Fact T.Obj (Reading T)) (K : List Fact) (content : Fact → T.Content) where
  identity_of_content : ∀ {f g}, f ∈ K → g ∈ K → content f = content g → f = g
  preserves : Fact → Fact → Prop
  refl : ∀ f, preserves f f
  trans : ∀ {f g h}, preserves f g → preserves g h → preserves f h
  mutual_content : ∀ {f g}, preserves f g → preserves g f → content f = content g
  record : {p c : Fact} → P.Occurrence p c → OccurrenceRecord T
  readAt : Fact → Reading T → T.Occ → Option (OccurrenceKind × T.Role × Fact)
  parentFull : ∀ {p c} (w : P.Occurrence p c), P.Full p (record w).parentText
  atAddress : ∀ {p c} (w : P.Occurrence p c),
    readAt p (record w).parentText (record w).address =
      some ((record w).kind, (record w).role, c)
  keeps : ∀ {p c}, P.Occurrence p c → preserves p c
  /-- Отдельный экземпляр утверждённого отношения данного родителя. -/
  Relation : Fact → Type
  participates : {p : Fact} → Relation p → T.Occ → T.Role → Prop

namespace ContractGraph

variable {T : LemmaOne.State} {Fact : Type} {P : Presentation Fact T.Obj (Reading T)}
    {K : List Fact} {content : Fact → T.Content}

def Represents (_G : ContractGraph T P K content) (f : Fact) (addr : T.Occ) (v : String) : Prop :=
  f ∈ K ∧ T.interpret addr v = some (content f)

/-- L_T(f): интерпретация лексической конструкции подтверждена в контексте. -/
def Family (G : ContractGraph T P K content) (f : Fact) (v : String) : Prop :=
  ∃ addr, G.Represents f addr v

/-- Обозначение объекта подтверждено в зафиксированном предъявлении
факта по адресу, доступному до поиска и раскрытия (§§2.2, 3.1–3.2). -/
def RecordedObject (G : ContractGraph T P K content) (f : Fact) (o : T.Obj) : Prop :=
  ∃ addr v, ∃ h : G.Represents f addr v, P.Designates ⟨addr, v, content f, h.2⟩ o

/-- В E_K сохраняем конкретное свидетельство, оба конца в K и их различие.
Таким образом, петля не возникает даже при адресной ссылке факта на себя. -/
def Edge (_G : ContractGraph T P K content) (p c : Fact) :=
  {_w : P.Occurrence p c // p ∈ K ∧ c ∈ K ∧ p ≠ c}

/-- Верхнее основание именно всего контракта. -/
def IsTop (G : ContractGraph T P K content) (f : Fact) : Prop :=
  f ∈ K ∧ ∀ p, ¬ Nonempty (G.Edge p f)

def CommonRelation (G : ContractGraph T P K content) {p x y : Fact}
    (left : P.Occurrence p x) (right : P.Occurrence p y) : Prop :=
  ∃ relation : G.Relation p,
    G.participates relation (G.record left).address (G.record left).role ∧
    G.participates relation (G.record right).address (G.record right).role

end ContractGraph
end SemanticChains
