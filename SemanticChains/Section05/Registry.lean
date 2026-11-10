import Std.Data.ExtTreeSet
import SemanticChains.ContractGraph

/-! §5.1. Конечный положительный реестр одного состояния контракта. -/
namespace SemanticChains.Section05

open Std
attribute [local instance] lexOrd

/-- До регистрации аргумент-факт указывает на предыдущую запись; после
разрешения он содержит канонический идентификатор её полного содержания. -/
inductive Argument (Ref : Type) where
  | object (id : Nat)
  | event (id : Nat)
  | fact (id : Ref)
  deriving DecidableEq, Repr

private def Argument.orderKey : Argument Nat → Nat × Nat
  | .object i => (0, i)
  | .event i => (1, i)
  | .fact i => (2, i)

instance : Ord (Argument Nat) := ⟨compareOn Argument.orderKey⟩
instance : TransOrd (Argument Nat) := inferInstanceAs (TransCmp (compareOn Argument.orderKey))
instance : LawfulEqOrd (Argument Nat) where
  eq_of_compare {a b} h := by
    have eq : a.orderKey = b.orderKey := LawfulEqOrd.eq_of_compare h
    cases a <;> cases b <;> simp_all [Argument.orderKey]

/-- Символ отношения и упорядоченный список его участников. -/
abbrev Atom (Ref : Type) := String × List (Argument Ref)
abbrev Content := ExtTreeSet (Atom Nat)

instance : DecidableEq Content := fun a b =>
  decidable_of_iff (a.toList = b.toList) ExtTreeSet.toList_inj

/-- В данном реестре первое вхождение содержания служит его устойчивым
идентификатором. В атомы попадают только идентификаторы зарегистрированных фактов. -/
def factId (history : List Content) (i : Fin history.length) : Nat :=
  history.idxOf (history.get i)

private theorem read_id (history : List Content) (i : Fin history.length) :
    history[factId history i]? = some (history.get i) := by
  have mem := List.getElem_mem (l := history) i.isLt
  have lt := List.idxOf_lt_length_of_mem mem
  have found := List.findIdx_getElem (p := (· == history.get i)) (xs := history) (w := lt)
  rw [List.getElem?_eq_getElem (show factId history i < history.length from lt)]
  exact congrArg some (eq_of_beq found)

theorem factId_eq_iff (history : List Content) (i j : Fin history.length) :
    factId history i = factId history j ↔ history.get i = history.get j := by
  constructor
  · intro same
    have h := read_id history i
    rw [same, read_id] at h
    exact (Option.some.inj h).symm
  · exact congrArg history.idxOf

theorem factId_stable (history more : List Content) (i : Fin history.length) :
    factId (history ++ more) ⟨i.val, by simp; omega⟩ = factId history i := by
  simp [factId, List.get_eq_getElem, List.getElem_append_left, i.isLt, List.idxOf_append]

/-- Разрешение имён фиксировано. В обоих видах полного вхождения адресат
предшествует записи. Простое упоминание выражается собственным атомом. -/
inductive Target (names : String → Option Nat) (n : Nat) where
  | included (index : Fin n)
  | reference (name : String) (index : Fin n) (resolved : names name = some index.val)

def Target.index {names n} : Target names n → Fin n
  | .included i | .reference _ i _ => i

structure Entry (names : String → Option Nat) (history : List Content) where
  own : List (Atom (Fin history.length))
  inclusions : List (String × Target names history.length)

def Entry.resolveAtom (history : List Content) (a : Atom (Fin history.length)) : Atom Nat :=
  (a.1, a.2.map fun arg => match arg with
    | .object id => .object id
    | .event id => .event id
    | .fact i => .fact (factId history i))

def Entry.content {names history} (u : Entry names history) : Content :=
  ExtTreeSet.ofList (u.own.map (Entry.resolveAtom history) ++
    u.inclusions.flatMap (fun link => (history.get link.2.index).toList))

/-- Определяющее объединение Own(u) и содержаний всех полных вхождений.
Ссылка внутри аргумента атома не добавляет сюда отдельного слагаемого. -/
theorem Entry.mem_content {names history} (u : Entry names history) (a : Atom Nat) :
    a ∈ u.content ↔ a ∈ u.own.map (Entry.resolveAtom history) ∨
      ∃ link ∈ u.inclusions, a ∈ history.get link.2.index := by
  simp [Entry.content, ExtTreeSet.mem_ofList, ExtTreeSet.mem_toList]

theorem same_fact_iff (history : List Content) (u v : Fin history.length) :
    history.get u = history.get v ↔ ∀ a, a ∈ history.get u ↔ a ∈ history.get v :=
  ⟨fun eq _ => eq ▸ Iff.rfl, ExtTreeSet.ext_mem⟩

theorem Entry.without_inclusions {names history} (u : Entry names history)
    (none : u.inclusions = []) (a : Atom Nat) :
    a ∈ u.content ↔ a ∈ u.own.map (Entry.resolveAtom history) := by
  simp [u.mem_content, none]

/-- Каждое расширение вычисляет содержание один раз из готового префикса.
Пустое утверждение не регистрируется. -/
inductive Registry (names : String → Option Nat) : List Content → Type where
  | empty : Registry names []
  | add {history} (previous : Registry names history) (entry : Entry names history)
      (nonempty : entry.content ≠ ∅) : Registry names (history ++ [entry.content])

def resolveFact (names : String → Option Nat) (history : List Content) (name : String) : Option Content :=
  (names name).bind (fun i => history[i]?)

theorem Registry.registered_nonempty {names history} (registry : Registry names history) :
    ∀ f ∈ history, f ≠ ∅ := by
  induction registry with
  | empty => simp
  | add previous entry nonempty ih =>
    intro f hf
    rcases List.mem_append.mp hf with old | new
    · exact ih f old
    · exact List.mem_singleton.mp new ▸ nonempty

theorem reference_resolves {names : String → Option Nat} {history : List Content}
    {name : String} {i : Fin history.length} (resolved : names name = some i.val) :
    resolveFact names history name = some (history.get i) := by
  simp [resolveFact, resolved, List.get_eq_getElem]

/-- Учитываются все исходные записи. latest хранит позицию в списке
вхождений (вместе с ролью и видом ссылки), earlier сохраняет исходный адрес
при последующих регистрациях. Вершины уже канонизированы по содержанию. -/
inductive Occurrence {names : String → Option Nat} :
    {history : List Content} → Registry names history → Content → Content → Type where
  | latest {history} {previous : Registry names history} {entry : Entry names history}
      {nonempty} (slot : Fin entry.inclusions.length) :
      Occurrence (.add previous entry nonempty) entry.content
        (history.get (entry.inclusions.get slot).2.index)
  | earlier {history} {previous : Registry names history} {entry : Entry names history}
      {nonempty p c} (w : Occurrence previous p c) :
      Occurrence (.add previous entry nonempty) p c

/-- Номер исходной записи и позиция внутри неё различают свидетельства,
включая несколько вхождений с одинаковыми концами. -/
def Occurrence.address {names history} {registry : Registry names history} {p c} :
    Occurrence registry p c → Nat × Nat
  | .latest (history := prefixRows) slot => (prefixRows.length, slot.val)
  | .earlier w => w.address

def Occurrence.roleAndKind {names history} {registry : Registry names history} {p c} :
    Occurrence registry p c → String × OccurrenceKind
  | .latest (entry := entry) slot =>
    let (role, target) := entry.inclusions.get slot
    (role, match target with | .included _ => .inclusion | .reference .. => .reference)
  | .earlier w => w.roleAndKind

theorem Occurrence.endpoints {names history} {registry : Registry names history} {p c}
    (w : Occurrence registry p c) : p ∈ history ∧ c ∈ history := by
  induction w with
  | latest slot =>
    exact ⟨by simp, List.mem_append_left _ (List.getElem_mem _)⟩
  | earlier _ ih => exact ⟨List.mem_append_left _ ih.1, List.mem_append_left _ ih.2⟩

/-- Внутренние вхождения одного факта остаются в Occurrence.
Строгое ребро графа соединяет различные канонические факты. -/
abbrev Edge {names history} (registry : Registry names history) (p c : Content) :=
  {_w : Occurrence registry p c // p ≠ c}

def Preserves (p c : Content) : Prop := ∀ a ∈ c, a ∈ p

theorem preserves_antisymm {p c : Content} (pc : Preserves p c) (cp : Preserves c p) : p = c :=
  ExtTreeSet.ext_mem (fun a => ⟨cp a, pc a⟩)

theorem occurrence_preserves {names history} {registry : Registry names history} {p c : Content}
    (w : Occurrence registry p c) : Preserves p c := by
  induction w with
  | latest slot =>
    intro a ha
    exact (Entry.mem_content _ _).2 (Or.inr ⟨_, List.getElem_mem slot.isLt, ha⟩)
  | earlier _ ih => exact ih

/-- Утверждение 5.1. Вдоль строгого ребра множество атомов строго
уменьшается, в частности уменьшается число различных атомов. -/
theorem edge_strict {names history} {registry : Registry names history} {p c : Content}
    (edge : Edge registry p c) : Preserves p c ∧ ¬ Preserves c p ∧ c.size < p.size := by
  have incl := occurrence_preserves edge.val
  have strict : ¬ Preserves c p := fun back => edge.property (preserves_antisymm incl back)
  have filtered : p.filter c.contains = c := by
    apply ExtTreeSet.ext_mem
    intro a
    simp only [ExtTreeSet.mem_filter, ExtTreeSet.get_eq, ExtTreeSet.contains_iff_mem]
    exact ⟨fun ⟨_, hc⟩ => hc, fun hc => ⟨incl a hc, hc⟩⟩
  have le := ExtTreeSet.size_filter_le_size (t := p) (f := c.contains)
  rw [filtered] at le
  refine ⟨incl, strict, Nat.lt_of_le_of_ne le ?_⟩
  intro eq
  have sameSize : (p.filter c.contains).size = p.size := (congrArg ExtTreeSet.size filtered).trans eq
  have all := ExtTreeSet.size_filter_eq_size_iff.mp sameSize
  apply strict
  intro a ha
  simpa using all a ha

theorem no_return {names history} {registry : Registry names history} {p c : Content}
    (edge : Edge registry p c) : ¬ Nonempty (Path (Edge registry) c p) := by
  have decreases {x y} (path : Path (Edge registry) x y) : y.size ≤ x.size := by
    induction path with
    | here => exact Nat.le_refl _
    | step e _ ih => exact Nat.le_trans ih (Nat.le_of_lt (edge_strict e).2.2)
  rintro ⟨back⟩
  exact (Nat.not_le_of_gt (edge_strict edge).2.2) (decreases back)

#print axioms Entry.mem_content
#print axioms factId_eq_iff
#print axioms edge_strict
#print axioms no_return

end SemanticChains.Section05
