import SemanticChains.Section02.AnswerGraph
import SemanticChains.Section05.Representation

/-! Полное предъявление бинарного факта и отдельная проверка сокращения по П3. -/
namespace SemanticChains.Section05

open Std
attribute [local instance] lexOrd

/-- Собственные атомы родителя фиксируют отношение, порядок его аргументов
и условия. Каждый подфакт входит со всем своим содержанием. -/
def binaryContent (left right : Content) (asserted : List (Atom Nat)) : Content :=
  ExtTreeSet.ofList (left.toList ++ right.toList ++ asserted)

theorem binary_content_iff (v left right : Content) (asserted : List (Atom Nat)) :
    v = binaryContent left right asserted ↔
    Preserves v left ∧ Preserves v right ∧ (∀ a ∈ asserted, a ∈ v) ∧
      Preserves (binaryContent left right asserted) v := by
  have mem (a : Atom Nat) : a ∈ binaryContent left right asserted ↔
      (a ∈ left ∨ a ∈ right) ∨ a ∈ asserted := by simp [binaryContent, or_assoc]
  constructor
  · rintro rfl
    exact ⟨fun a h => (mem a).2 (Or.inl (Or.inl h)), fun a h => (mem a).2 (Or.inl (Or.inr h)),
      fun a h => (mem a).2 (Or.inr h), fun _ h => h⟩
  · rintro ⟨l, r, relations, onlyParent⟩
    apply ExtTreeSet.ext_mem
    intro a
    exact ⟨onlyParent a, fun h => ((mem a).1 h).elim (fun e => e.elim (l a) (r a)) (relations a)⟩

namespace BinaryExample

private def water : Atom Nat := ("FinishWatering", [.event 1, .object 1])
private def meet : Atom Nat := ("GoMeetFriends", [.event 2, .object 2])
private def whenRel : Atom Nat := ("When", [.event 1, .event 2])
private def causeRel : Atom Nat := ("Cause", [.event 2, .event 1])

def watering : Content := ExtTreeSet.ofList [water]
def meeting : Content := ExtTreeSet.ofList [meet]
def temporal := binaryContent watering meeting [whenRel]
def causal := binaryContent watering meeting [causeRel]
def eventsOnly := binaryContent watering meeting []

private def original := "When Emma finished watering, Kyle went to meet his friends."
private def thenText := "Emma finished watering, and then Kyle went to meet his friends."
private def becauseText := "Kyle went to meet his friends, so Emma finished watering."
private def twoSentences := "Emma finished watering. Kyle went to meet his friends."

/-- Вход примера — уже установленное чтение нескольких конкретных
вхождений. Другие сочетания адреса и слов не получают чтения автоматически. -/
private def occurrences : List ((Nat × String) × Content) :=
  [((0, original), temporal), ((1, thenText), temporal), ((2, becauseText), causal),
   ((3, twoSentences), eventsOnly), ((4, twoSentences), temporal),
   ((5, "xxx"), temporal), ((6, "xx"), eventsOnly), ((7, "x"), eventsOnly)]

private abbrev state : LemmaOne.State where
  Obj := Nat
  Occ := Nat
  Role := String
  Content := Content
  interpret pos words := occurrences.lookup (pos, words)
  Requirement := Unit
  questionRole := fun _ _ => some "participant"
  answerRole := fun _ _ => some "participant"
  resolve := fun _ => some 1
  requests := fun _ _ => True
  supplies := fun _ _ => True
  recovers := fun _ _ a => a = eventsOnly

private abbrev Text := Reading state
private def whenV : Text := ⟨0, original, temporal, rfl⟩
private def thenV : Text := ⟨1, thenText, temporal, rfl⟩
private def causeV : Text := ⟨2, becauseText, causal, rfl⟩
private def listV : Text := ⟨3, twoSentences, eventsOnly, rfl⟩
/-- Дополнительный контроль: в позиции 4 контекст явно задаёт временную связь. -/
private def contextualV : Text := ⟨4, twoSentences, temporal, rfl⟩
private def longV : Text := ⟨5, "xxx", temporal, rfl⟩
private def middleV : Text := ⟨6, "xx", eventsOnly, rfl⟩
private def lastV : Text := ⟨7, "x", eventsOnly, rfl⟩

private inductive Slot : Content → Content → Type where
  | left : Slot temporal watering
  | right : Slot temporal meeting

private theorem slot_preserves {p c} (slot : Slot p c) : Preserves p c := by
  have included := (binary_content_iff temporal watering meeting [whenRel]).1 rfl
  cases slot with
  | left => exact included.1
  | right => exact included.2.1

private def presentation : Presentation Content Nat Text where
  Occurrence := Slot
  Full f v := v.textContent = f
  Designates v o := v.address ≠ 6 ∧ ∃ a ∈ v.textContent, Argument.object o ∈ a.2
  expand _ _ := whenV
  full_expand := by intro p c w v _; cases w <;> rfl
  retains_designation := by
    rintro p c w v o full ⟨_, a, ha, arg⟩
    have mem := slot_preserves w a (full ▸ ha)
    cases w <;> exact ⟨by decide, a, mem, arg⟩

private def facts := [temporal, causal, eventsOnly, watering, meeting]

private def graph : ContractGraph state presentation facts id where
  identity_of_content := fun _ _ eq => eq
  preserves := Preserves
  refl := fun _ _ h => h
  trans := fun first second a h => first a (second a h)
  mutual_content := preserves_antisymm
  record w := match w with
    | .left => ⟨whenV, 8, "When.first", .inclusion⟩
    | .right => ⟨whenV, 9, "When.second", .inclusion⟩
  readAt _ v addr := if v.address = 0 then
      match addr with
      | 8 => some (.inclusion, "When.first", watering)
      | 9 => some (.inclusion, "When.second", meeting)
      | _ => none
    else none
  parentFull w := by cases w <;> rfl
  atAddress w := by cases w <;> rfl
  keeps := slot_preserves
  Relation := fun p => PLift (p = temporal)
  participates := fun _ pos role => (pos = 8 ∧ role = "When.first") ∨ (pos = 9 ∧ role = "When.second")

private def model : ChainModel state Content (Atom Nat → Prop) where
  registered := facts
  presentation := presentation
  factContent := id
  graph := graph
  full_for_recorded_object := by
    rintro f o ⟨addr, words, h, key⟩
    exact ⟨⟨addr, words, f, h.2⟩, rfl, key⟩
  holds := fun f i => Holds i f
  preservation_sound := fun incl => entails_of_preserves incl
  full_iff := Iff.rfl
  questionFactMention := fun _ _ => none
  expresses := fun _ a f => Preserves f a
  contributes := fun _ a _ l _ => Preserves l.2.textContent a
  full_contributes := fun role full => full ▸ role
  faithfulEdit := fun f v u => f = temporal ∧
    ((v.address = 0 ∧ u.address = 3) ∨
     (v.address = 5 ∧ u.address = 6) ∨ (v.address = 6 ∧ u.address = 7))

theorem full_temporal_iff (v : Text) :
    model.presentation.Full temporal v ↔ Preserves v.textContent watering ∧
    Preserves v.textContent meeting ∧ (∀ a ∈ [whenRel], a ∈ v.textContent) ∧
    Preserves temporal v.textContent :=
  model.full_iff.trans (binary_content_iff v.textContent watering meeting [whenRel])

theorem same_temporal_parent : model.presentation.Full temporal whenV ∧
    model.presentation.Full temporal thenV := ⟨rfl, rfl⟩

theorem temporal_roles : model.graph.CommonRelation Slot.left Slot.right := by
  exact ⟨⟨rfl⟩, Or.inl ⟨rfl,rfl⟩, Or.inr ⟨rfl,rfl⟩⟩

theorem changed_or_omitted_relation :
    model.presentation.Full causal causeV ∧ ¬ model.presentation.Full temporal causeV ∧
    model.presentation.Full eventsOnly listV ∧ ¬ model.presentation.Full temporal listV := by
  exact ⟨rfl, by change causal ≠ temporal; decide, rfl, by change eventsOnly ≠ temporal; decide⟩

theorem same_words_two_verified_readings :
    listV.wording = contextualV.wording ∧ listV.address ≠ contextualV.address ∧
    ¬ model.presentation.Full temporal listV ∧ model.presentation.Full temporal contextualV :=
  ⟨rfl, by decide, changed_or_omitted_relation.2.2.2, rfl⟩

/-- Смена порядка ролей или добавление совместно не утверждённого
условия тоже меняет полное содержание при тех же двух подфактах. -/
theorem roles_and_conditions_matter :
    binaryContent watering meeting [("When", [.event 2, .event 1])] ≠ temporal ∧
    binaryContent watering meeting [whenRel, ("OnlyAtNight", [.event 2])] ≠ temporal := by decide

private def E : Expansion model := ⟨temporal, fun _ => True⟩
private def Q := "What two actions did Emma and Kyle perform?"

private theorem events_follow : Preserves temporal eventsOnly := by
  intro a h
  simp [eventsOnly, temporal, binaryContent] at h ⊢
  exact h.elim Or.inl (fun right => Or.inr (Or.inl right))

private theorem current (v : Text) (enough : Preserves v.textContent eventsOnly)
    (visible : presentation.Designates v 1) :
    model.SupportsNow E Q eventsOnly [(temporal,v)] [1,1] 1 := by
  have q : LemmaOne.InQuestion state Q 1 := ⟨0, "participant", rfl, rfl⟩
  have a : LemmaOne.InFullAnswer state eventsOnly 1 := ⟨0, "participant", rfl, rfl⟩
  refine ⟨by simp, by simp, ?_, ?_, ?_, trivial, ⟨q, visible, visible, a, trivial⟩,
    q, a, _, List.mem_cons_self, visible⟩
  · intro l member
    obtain rfl := List.mem_singleton.mp member
    exact E.root_mem
  · intro pre l post split
    have mem : l ∈ [(temporal,v)] := split ▸ (by simp)
    exact List.mem_singleton.mp mem ▸ enough
  · intro i all
    exact entails_of_preserves enough i (all _ List.mem_cons_self)

private theorem when_visible : presentation.Designates whenV 1 :=
  ⟨by decide, water, by decide, by decide⟩
private theorem list_visible : presentation.Designates listV 1 :=
  ⟨by decide, water, by decide, by decide⟩

/-- Перечисление подходит по П3 для вопроса о двух действиях. Основание
всё ещё temporal, а текст утратил временное отношение родителя. -/
theorem admissible_shortening_for_actions :
    model.Supports E Q eventsOnly [(temporal,listV)] [1,1] 1 ∧
    ¬ model.presentation.Full temporal listV := by
  have start : model.Supports E Q eventsOnly [(temporal,whenV)] [1,1] 1 :=
    .full (by simpa using same_temporal_parent.1) (current whenV events_follow when_visible)
  have cut : model.Cut temporal whenV listV :=
    ⟨⟨rfl, Or.inl ⟨rfl,rfl⟩⟩, entails_of_preserves events_follow, by decide⟩
  exact ⟨.shorten (pre := []) (post := []) start cut
    (current listV (fun _ => id) list_visible), changed_or_omitted_relation.2.2.2⟩

theorem listing_does_not_justify_time :
    ¬ model.Entails listV.textContent temporal := by
  intro entail
  have holdsParent := entail (fun a => a ∈ eventsOnly) (fun _ => id)
  exact (by decide : whenRel ∉ eventsOnly) (holdsParent whenRel (by decide))

theorem raw_gap_steps : Edits (model.Cut temporal) longV lastV :=
  .snoc (u := middleV) (.snoc .refl ⟨⟨rfl, Or.inr (Or.inl ⟨rfl,rfl⟩)⟩, entails_of_preserves events_follow, by decide⟩)
    ⟨⟨rfl, Or.inr (Or.inr ⟨rfl,rfl⟩)⟩, fun _ => id, by decide⟩

private theorem no_checked_gap (keys : List state.Obj) (common : state.Obj) :
    ¬ model.Supports E Q eventsOnly [(temporal,lastV)] keys common := by
  intro valid
  generalize eq : [(temporal,lastV)] = result at valid
  cases valid with
  | full all _ =>
    have member : (temporal,lastV) ∈ _ := eq ▸ List.mem_cons_self
    exact (by decide : eventsOnly ≠ temporal) (all _ member)
  | @shorten pre post f v u keys o previous cut _ =>
    obtain ⟨rfl, same, rfl⟩ : pre = [] ∧ (f,u) = (temporal,lastV) ∧ post = [] := by
      simpa [List.singleton_eq_append_iff, and_assoc] using eq
    cases same
    have blocked : v.address = 6 := by
      rcases cut.1.2 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩
      · exact False.elim ((by decide : lastV.address ≠ 3) h)
      · exact False.elim ((by decide : lastV.address ≠ 6) h)
      · exact h
    obtain ⟨_, _, _, _, _, _, _, _, _, link, mem, visible⟩ := previous.now
    obtain rfl := List.mem_singleton.mp mem
    exact visible.1 blocked

/-- Проверка разрыва «xxx → xx → x». Конечный набор сам по себе годится;
при любом выборе ключей единственный предшественник x лишён обозначения. -/
theorem gap_rejected :
    model.SupportsNow E Q eventsOnly [(temporal,lastV)] [1,1] 1 ∧
    ∀ o, ¬ model.Admissible E Q eventsOnly [(temporal,lastV)] o := by
  refine ⟨current lastV (fun _ => id) ⟨by decide, water, by decide, by decide⟩, ?_⟩
  rintro o ⟨keys, path, _⟩
  exact no_checked_gap keys o path

#print axioms admissible_shortening_for_actions
#print axioms gap_rejected

end BinaryExample
end SemanticChains.Section05
