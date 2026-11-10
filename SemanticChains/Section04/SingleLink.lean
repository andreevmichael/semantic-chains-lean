import SemanticChains.Presentation

/-! §4.2. Текстовое представление основания и существование однозвенной цепочки.
Все утверждения относятся к одному фиксированному состоянию контракта и выбранному разбору. -/

namespace SemanticChains

/-- Lemma 4.2.1. Starting from the full text at the endpoint, construct
a full root text designating the same object. -/
theorem present_at_root {Fact Obj Text : Type} (m : Presentation Fact Obj Text)
    {r f : Fact} (path : Path m.Occurrence r f) {o : Obj} {v : Text}
    (full : m.Full f v) (key : m.Designates v o) :
    ∃ text : Text, m.Full r text ∧ m.Designates text o := by
  induction path with
  | here => exact ⟨v, full, key⟩
  | step w tail ih =>
    obtain ⟨childText, childFull, childKey⟩ := ih full
    exact ⟨m.expand w childText, m.full_expand w childFull,
      m.retains_designation w childFull childKey⟩

#print axioms present_at_root

/-- At this proof step a preserving edge has a semantic consequence (T9.4).
Its occurrence witness is still required. The converse is not assumed.
An interpretation ranges over the admissible interpretations of this state
and need not satisfy every assertion in the contract. -/
structure Semantics {Fact Obj : Type} (m : Presentation Fact Obj) (Interp : Type) where
  factHolds : Fact → Interp → Prop
  textHolds : String → Interp → Prop
  edge_sound : ∀ {p c : Fact}, m.Occurrence p c →
    ∀ I, factHolds p I → factHolds c I
  full_meaning : ∀ {f : Fact} {v : String}, m.Full f v →
    ∀ I, textHolds v I ↔ factHolds f I

/-- The edges in a path may be just the selected expansion edges E′ (§3.4). -/
theorem path_sound {Fact Obj Interp : Type} {m : Presentation Fact Obj}
    (sem : Semantics m Interp) {r f : Fact} (path : Path m.Occurrence r f) :
    ∀ I, sem.factHolds r I → sem.factHolds f I := by
  induction path with
  | here => exact fun _ hr => hr
  | step w _ ih => exact fun I hr => ih I (sem.edge_sound w I hr)

/-- §4.2, before minimization. S is the expansion reachable from the chosen
root r. Sufficiency uses precisely those facts. Q and answer are the texts
of the question and of the full answer Â in the fixed state. -/
theorem justified_root_text {Fact Obj Interp : Type} {m : Presentation Fact Obj}
    (sem : Semantics m Interp) {r f : Fact} {o : Obj} {v Q answer : String}
    (enough : ∀ I, (∀ g, Nonempty (Path m.Occurrence r g) → sem.factHolds g I) →
      sem.textHolds answer I)
    (path : Path m.Occurrence r f) (full : m.Full f v) (key : m.Designates v o)
    (inQuestion : m.Designates Q o) (inAnswer : m.Designates answer o) :
    ∃ text : String, m.Full r text ∧
      (∀ I, sem.textHolds text I → sem.textHolds answer I) ∧
      m.Designates Q o ∧ m.Designates text o ∧ m.Designates answer o := by
  obtain ⟨text, fullRoot, rootKey⟩ := present_at_root m path full key
  refine ⟨text, fullRoot, ?_, inQuestion, rootKey, inAnswer⟩
  intro I ht
  have hr := (sem.full_meaning fullRoot I).mp ht
  apply enough I
  intro g reachable
  obtain ⟨toFact⟩ := reachable
  exact path_sound sem toFact I hr

#print axioms path_sound
#print axioms justified_root_text

/-- P3 and P5 are interpreted in the fixed contract. A faithful edit keeps
the required asserted content in its role, status and scope at the same
underlying fact. Contribution is judged against the particular question
and full answer. A full representation presents the fact's contribution. -/
structure LinkRules {Fact Obj : Type} (m : Presentation Fact Obj) where
  faithfulEdit : Fact → String → String → Prop
  factContributes : (Q answer : String) → Fact → Prop
  textContributes : (Q answer : String) → Fact → String → Prop
  full_contribution : ∀ {Q answer r v}, m.Full r v →
    factContributes Q answer r → textContributes Q answer r v

/-- Conditions that must still hold after each edit of the sole link. -/
structure LinkContent {Fact Obj Interp : Type} {m : Presentation Fact Obj}
    (sem : Semantics m Interp) (rules : LinkRules m)
    (Q answer : String) (r : Fact) (o : Obj) (text : String) : Prop where
  sufficient : ∀ I, sem.textHolds text I → sem.textHolds answer I
  contributes : rules.textContributes Q answer r text
  designates : m.Designates text o

/-- Only the text changes. The new assertion follows from the old one
without other premises (P3). Length counts characters in the fixed text (P6). -/
structure AdmissibleCut {Fact Obj Interp : Type} {m : Presentation Fact Obj}
    (sem : Semantics m Interp) (rules : LinkRules m)
    (Q answer : String) (r : Fact) (o : Obj) (before after : String) : Prop where
  faithful : rules.faithfulEdit r before after
  entailed : ∀ I, sem.textHolds before I → sem.textHolds after I
  shorter : after.length < before.length
  result : LinkContent sem rules Q answer r o after

theorem exists_least_measure {α : Type} (measure : α → Nat) {P : α → Prop}
    (s : α) (hs : P s) : ∃ t, P t ∧ ∀ u, P u → measure t ≤ measure u := by
  classical
  by_cases smaller : ∃ u, P u ∧ measure u < measure s
  · obtain ⟨u, hu, hlt⟩ := smaller
    exact exists_least_measure measure u hu
  · exact ⟨s, hs, fun u hu => Nat.le_of_not_gt (fun h => smaller ⟨u, hu, h⟩)⟩
termination_by measure s

/-- A nonempty family of strings contains one of least character length. -/
theorem exists_shortest_text {P : String → Prop} (s : String) (hs : P s) :
    ∃ t, P t ∧ ∀ u, P u → t.length ≤ u.length :=
  exists_least_measure String.length s hs

/-- A shortest reachable text is still sufficient and admits no next
admissible cut. No finiteness assumption on the set of representations. -/
theorem minimize_link {Fact Obj Interp : Type} {m : Presentation Fact Obj}
    {sem : Semantics m Interp} {rules : LinkRules m} {Q answer : String}
    {r : Fact} {o : Obj} {start : String}
    (initial : LinkContent sem rules Q answer r o start) :
    let cut := AdmissibleCut sem rules Q answer r o
    ∃ best, Edits cut start best ∧ LinkContent sem rules Q answer r o best ∧
      (∀ t, Edits cut start t → best.length ≤ t.length) ∧
      (∀ t, ¬ cut best t) := by
  let cut := AdmissibleCut sem rules Q answer r o
  obtain ⟨best, reached, least⟩ := exists_shortest_text (P := Edits cut start) start .refl
  have content : LinkContent sem rules Q answer r o best := by
    cases reached with
    | refl => exact initial
    | snoc _ last => exact last.result
  refine ⟨best, reached, content, least, ?_⟩
  intro t next
  exact (Nat.not_lt_of_ge (least t (.snoc reached next))) next.shorter

/-- S4 at a boundary: both texts verifiably designate the same object. -/
def BoundaryKey {Fact Obj : Type} (m : Presentation Fact Obj)
    (left right : String) (o : Obj) : Prop :=
  m.Designates left o ∧ m.Designates right o

/-- The one-link case of §4.2. The list constructor fixes both its length
and its underlying fact. There is no internal pair of adjacent links. -/
inductive SingletonChain {Fact Obj Interp : Type} {m : Presentation Fact Obj}
    (sem : Semantics m Interp) (rules : LinkRules m)
    (Q answer : String) (r : Fact) (o : Obj) : List (Fact × String) → Prop where
  | link {start text : String} :
      m.Full r start →
      Edits (AdmissibleCut sem rules Q answer r o) start text →
      LinkContent sem rules Q answer r o text →
      BoundaryKey m Q text o → BoundaryKey m text answer o →
      (∀ t, ¬ AdmissibleCut sem rules Q answer r o text t) →
      SingletonChain sem rules Q answer r o [(r, text)]

/-- §4.2. Assume a selected sufficient expansion and a root contributing
the requested content. Construct the chain [Z*], including its two keys. -/
theorem exists_singleton_chain {Fact Obj Interp : Type} {m : Presentation Fact Obj}
    (sem : Semantics m Interp) (rules : LinkRules m)
    {Q answer v : String} {r f : Fact} {o : Obj}
    (rootRole : rules.factContributes Q answer r)
    (enough : ∀ I, (∀ g, Nonempty (Path m.Occurrence r g) → sem.factHolds g I) →
      sem.textHolds answer I)
    (path : Path m.Occurrence r f) (full : m.Full f v) (key : m.Designates v o)
    (inQuestion : m.Designates Q o) (inAnswer : m.Designates answer o) :
    ∃ text, SingletonChain sem rules Q answer r o [(r, text)] := by
  obtain ⟨start, fullRoot, justifies, questionKey, rootKey, answerKey⟩ :=
    justified_root_text sem enough path full key inQuestion inAnswer
  have initial : LinkContent sem rules Q answer r o start :=
    ⟨justifies, rules.full_contribution fullRoot rootRole, rootKey⟩
  obtain ⟨best, reached, content, _, minimal⟩ := minimize_link initial
  exact ⟨best, .link fullRoot reached content ⟨questionKey, content.designates⟩
    ⟨content.designates, answerKey⟩ minimal⟩

#print axioms minimize_link
#print axioms exists_singleton_chain

end SemanticChains
