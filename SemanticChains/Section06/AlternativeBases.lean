import SemanticChains.Section04.OrderEnumeration
import SemanticChains.Section05.Representation

/-! §6.4. Альтернативные обоснования одного полного ответа в фиксированном T. -/
namespace SemanticChains.Section06

open LemmaOne (State InQuestion InFullAnswer)
open Section04 (Absorptions Normal positions)

variable {T : State} {F I : Type} {M : ChainModel T F I}

/-- Данные одного предъявленного разбора. Достаточность относится к его
собственному S; носитель ключа также должен лежать в этом S. -/
structure AnswerBasis (E : Expansion M) (Q : String) (a : T.Content) : Prop where
  registered : E.root ∈ M.registered
  expresses : M.expresses Q a E.root
  sufficient : ∀ i, (∀ f, E.InS f → M.holds (M.factContent f) i) → M.holds a i
  carrier : ∃ f o, E.InS f ∧ M.graph.RecordedObject f o ∧ InQuestion T Q o ∧ InFullAnswer T a o

theorem AnswerBasis.possibleRoot {E : Expansion M} {Q a} (h : AnswerBasis E Q a) :
    M.PossibleRoot Q a E.root := by
  refine ⟨h.registered, h.expresses, ?_⟩
  intro i rootHolds
  apply h.sufficient i
  rintro f ⟨path⟩
  exact Section02.path_entails (Section02.contractPath path) i rootHolds

/-- Оба разбора находятся в одном W. Каждый независимо нормализуется до
своего основания и даёт собственное однозвенное предъявление ответа a.
Никаких условий на пересечение, равенство ключей или порядок поглощений. -/
theorem alternative_bases {Q a} (first second : Expansion M)
    (h₁ : AnswerBasis first Q a) (h₂ : AnswerBasis second Q a) :
    ∀ E ∈ [first, second],
      E.InS E.root ∧
      (∀ f, E.InS f → Section03.InW M (Section03.initialFacts M Q) f) ∧
      (∀ f, E.IsTop f ↔ f = E.root) ∧
      (∀ {n final}, Absorptions E.AnswerEdge n (positions E) final →
        Normal E.AnswerEdge final → final = [E.root]) ∧
      ∃ v o, M.Admissible E Q a [(E.root, v)] o := by
  intro E selected
  have checked : AnswerBasis E Q a := by
    rcases List.mem_cons.mp selected with eq | last
    · exact eq ▸ h₁
    · exact List.mem_singleton.mp last ▸ h₂
  obtain ⟨f, o, inside, recorded, inQ, inA⟩ := checked.carrier
  obtain ⟨_, covered, _, v, chain⟩ :=
    Section04.found_singleton_chain checked.possibleRoot inside recorded inQ inA
  exact ⟨E.root_mem, covered, fun _ => E.top_iff_root,
    fun steps done => Section04.normalized_eq_singleton E checked.registered steps done, v, o, chain⟩

/-- Если основание звена встречается лишь в одном разборе, одноимённый
порядок даже не является кандидатом в другом (§4.4). -/
theorem order_depends_on_basis {E D : Expansion M} {f : F}
    (hr : E.root ∈ M.registered) (hs : D.root ∈ M.registered)
    (present : E.InS f) (absent : ¬ D.InS f) :
    [f] ∈ Section04.candidates E ∧ [f] ∉ Section04.candidates D := by
  constructor
  · apply (Section04.mem_candidates E hr _).2
    by_cases eq : f = E.root
    · exact Or.inl (congrArg (fun x => [x]) eq)
    · exact Or.inr ⟨by simp, by simp, by simpa using And.intro present eq⟩
  · intro candidate
    rcases (Section04.mem_candidates D hs _).1 candidate with root | ⟨_, _, facts⟩
    · exact absent ((List.cons.inj root).1 ▸ D.root_mem)
    · exact absent (facts f List.mem_cons_self).1

namespace Figure

/-- Рис. 6.2. Выбираются только вхождения из r в перечисленных детей.
Каждое выбранное ребро по-прежнему требует свидетельства из контракта. -/
def branches (M : ChainModel T F I) (r : F) (children : List F) : Expansion M where
  root := r
  chosen := fun {p c} _ => p = r ∧ c ∈ children

private theorem mem_branch {r c : F} (edge : M.graph.Edge r c) (f : F) :
    (branches M r [c]).InS f ↔ f = r ∨ f = c := by
  constructor
  · rintro ⟨path⟩
    have endPoint {p y : F} (walk : Path (branches M r [c]).Edge p y) : y = p ∨ y = c := by
      induction walk with
      | here => exact Or.inl rfl
      | step w _ ih =>
        rcases ih with rfl | reached
        · exact Or.inr (List.mem_singleton.mp w.property.2)
        · exact Or.inr reached
    exact endPoint path
  · rintro (rfl | rfl)
    · exact (branches M _ _).root_mem
    · exact ⟨.step ⟨edge, rfl, List.mem_cons_self⟩ (.here _)⟩

theorem disjoint_branches {r s a b : F} (left : M.graph.Edge r a) (right : M.graph.Edge s b)
    (rs : r ≠ s) (rb : r ≠ b) (as' : a ≠ s) (ab : a ≠ b) :
    ∀ f, (branches M r [a]).InS f → ¬ (branches M s [b]).InS f := by
  intro f inLeft inRight
  rcases (mem_branch left f).1 inLeft with rfl | rfl <;>
    rcases (mem_branch right _).1 inRight with eq | eq <;> contradiction

theorem common_subfact {r s c : F} (left : M.graph.Edge r c) (right : M.graph.Edge s c)
    (distinct : r ≠ s) (f : F) :
    (branches M r [c]).InS f ∧ (branches M s [c]).InS f ↔ f = c := by
  rw [mem_branch left, mem_branch right]
  grind

theorem common_root {r a b : F} (left : M.graph.Edge r a) (right : M.graph.Edge r b)
    (distinct : a ≠ b) (f : F) :
    (branches M r [a]).InS f ∧ (branches M r [b]).InS f ↔ f = r := by
  rw [mem_branch left, mem_branch right]
  grind

/-- Если вопрос требует связи обоих детей, обе ветви включаются в один
разбор. Родитель остаётся свидетелем структурного соседства звеньев. -/
theorem joint_branches {r a b : F} (left : M.graph.Edge r a) (right : M.graph.Edge r b)
    (distinct : a ≠ b) (relation : M.graph.CommonRelation left.val right.val) :
    let E := branches M r [a,b]
    E.InS r ∧ E.InS a ∧ E.InS b ∧ E.Connected a b := by
  let E := branches M r [a,b]
  let ea : E.Edge r a := ⟨left, rfl, by simp⟩
  let eb : E.Edge r b := ⟨right, rfl, by simp⟩
  exact ⟨E.root_mem, E.mem_of_step E.root_mem ea, E.mem_of_step E.root_mem eb,
    Section02.connected_via_parent E.root_mem ea eb distinct relation⟩

end Figure

namespace DavidExample

open Std Section05
attribute [local instance] lexOrd

/-- C — Дэвид пришёл в зал. Имена C, R1, R2 однозначны внутри этого реестра. -/
private def names : String → Option Nat
  | "C" => some 0 | "R1" => some 1 | "R2" => some 2 | _ => none

def arrival : Entry names [] :=
  ⟨[("Arrive", [.event 1, .object 1, .object 2])], []⟩

def beforeMeeting : Entry names [arrival.content] :=
  ⟨[("MeetingStart", [.event 2]), ("Before", [.event 1, .event 2])],
   [("earlier event", .reference "C" ⟨0, by decide⟩ rfl)]⟩

def doorClosed : Entry names [arrival.content, beforeMeeting.content] :=
  ⟨[("CloseDoor", [.event 3, .object 3, .object 4]), ("Before", [.event 1, .event 3])],
   [("earlier event", .reference "C" ⟨0, by decide⟩ rfl)]⟩

private def registry : Registry names [arrival.content, beforeMeeting.content, doorClosed.content] :=
  Registry.add (Registry.add (Registry.add .empty arrival (by decide)) beforeMeeting (by decide))
    doorClosed (by decide)

/-- Два разных родителя сохраняют один C и по отдельности обосновывают
приход Дэвида. Дополнительное содержание каждого независимо от другого. -/
theorem two_accounts :
    (∀ I, Holds I beforeMeeting.content → Holds I arrival.content) ∧
    (∀ I, Holds I doorClosed.content → Holds I arrival.content) ∧
    (∃ I, Holds I beforeMeeting.content ∧ ¬ Holds I doorClosed.content) ∧
    (∃ I, Holds I doorClosed.content ∧ ¬ Holds I beforeMeeting.content) := by
  let left : Occurrence registry beforeMeeting.content arrival.content :=
    .earlier (.latest (entry := beforeMeeting) ⟨0, by decide⟩)
  let right : Occurrence registry doorClosed.content arrival.content :=
    .latest (entry := doorClosed) ⟨0, by decide⟩
  refine ⟨entails_of_preserves (occurrence_preserves left),
    entails_of_preserves (occurrence_preserves right), ?_, ?_⟩
  · refine ⟨fun a => a ∈ beforeMeeting.content, fun _ h => h, fun all => ?_⟩
    let close : Atom Nat := ("CloseDoor", [.event 3, .object 3, .object 4])
    exact (by decide +revert : close ∉ beforeMeeting.content) (all close (by decide +revert))
  · refine ⟨fun a => a ∈ doorClosed.content, fun _ h => h, fun all => ?_⟩
    let start : Atom Nat := ("MeetingStart", [.event 2])
    exact (by decide +revert : start ∉ doorClosed.content) (all start (by decide +revert))

end DavidExample

#print axioms alternative_bases
#print axioms order_depends_on_basis
#print axioms Figure.disjoint_branches
#print axioms Figure.common_subfact
#print axioms Figure.common_root
#print axioms Figure.joint_branches
#print axioms DavidExample.two_accounts

end SemanticChains.Section06
