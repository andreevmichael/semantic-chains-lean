import SemanticChains.Section05.RegistryExamples

/-! §6.3. Одна запись полного факта для всех его повторных предъявлений.
Область действия отношения и позиция каждого участника остаются в схеме раскрытия. -/
namespace SemanticChains.Section06

open Section05 Std
attribute [local instance] lexOrd

/-- Key обозначает вложенный факт. Узлы дерева хранят атомы отношений,
группировку частей и индивидуальные свидетельства участия. -/
inductive Disclosure (Key Evidence : Type) where
  | fact (key : Key)
  | assertion (atom : Atom Nat)
  | atSlot (witness : Evidence) (part : Disclosure Key Evidence)
  | both (left right : Disclosure Key Evidence)

namespace Disclosure
variable {K L W : Type}

def facts : Disclosure K W → List K
  | .fact k => [k]
  | .assertion _ => []
  | .atSlot _ v => v.facts
  | .both x y => x.facts ++ y.facts

def assertions : Disclosure K W → List (Atom Nat)
  | .fact _ => []
  | .assertion a => [a]
  | .atSlot _ v => v.assertions
  | .both x y => x.assertions ++ y.assertions

def mapFacts (f : K → L) : Disclosure K W → Disclosure L W
  | .fact k => .fact (f k)
  | .assertion a => .assertion a
  | .atSlot w v => .atSlot w (v.mapFacts f)
  | .both x y => .both (x.mapFacts f) (y.mapFacts f)

def readFacts (read : K → Option L) : Disclosure K W → Option (Disclosure L W)
  | .fact k => (read k).map .fact
  | .assertion a => some (.assertion a)
  | .atSlot w v => (v.readFacts read).map (.atSlot w)
  | .both x y => return .both (← x.readFacts read) (← y.readFacts read)

private theorem read_map {code : K → L} {read : L → Option K} (v : Disclosure K W)
    (ok : ∀ k ∈ v.facts, read (code k) = some k) :
    (v.mapFacts code).readFacts read = some v := by
  induction v with
  | fact k => simp [mapFacts, readFacts, ok k List.mem_cons_self]
  | assertion => rfl
  | atSlot w v ih => simp [mapFacts, readFacts, ih ok]
  | both x y ix iy =>
    simp [mapFacts, readFacts, ix (fun k hk => ok k (List.mem_append_left _ hk)),
      iy (fun k hk => ok k (List.mem_append_right _ hk))]

private theorem assertions_map (v : Disclosure K W) (f : K → L) :
    (v.mapFacts f).assertions = v.assertions := by
  induction v <;> simp_all [mapFacts, assertions]

end Disclosure

/-- Унификация только по полному содержанию §5.1. Номера в таблице
локальны для этого предъявления; идентификаторы целых фактов внутри
атомов отношений остаются идентификаторами исходного реестра. -/
structure SharedDisclosure (W : Type) where
  table : List Content
  layout : Disclosure Nat W

private def distinctFacts : List Content → List Content
  | [] => []
  | x :: xs => (distinctFacts xs).insert x

private theorem distinct_spec (xs : List Content) :
    (distinctFacts xs).Nodup ∧ ∀ f, f ∈ distinctFacts xs ↔ f ∈ xs := by
  induction xs with
  | nil => simp [distinctFacts]
  | cons x xs ih =>
    constructor
    · by_cases present : x ∈ distinctFacts xs
      · simpa [distinctFacts, present] using ih.1
      · simpa [distinctFacts, present] using ih.1
    · intro f
      simp [distinctFacts, List.mem_insert_iff, ih.2]

def share {W : Type} (v : Disclosure Content W) : SharedDisclosure W :=
  let table := distinctFacts v.facts
  ⟨table, v.mapFacts table.idxOf⟩

def SharedDisclosure.restore {W : Type} (s : SharedDisclosure W) :=
  s.layout.readFacts (fun i => s.table[i]?)

private theorem read_index (table : List Content) {f : Content} (hf : f ∈ table) :
    table[table.idxOf f]? = some f := by
  have lt := List.idxOf_lt_length_of_mem hf
  rw [List.getElem?_eq_getElem lt]
  exact congrArg some (eq_of_beq (List.findIdx_getElem (p := (· == f)) (xs := table) (w := lt)))

theorem same_slot_iff {W : Type} (v : Disclosure Content W) {f g : Content}
    (hf : f ∈ v.facts) (hg : g ∈ v.facts) :
    (share v).table.idxOf f = (share v).table.idxOf g ↔ f = g := by
  have catalog := (distinct_spec v.facts).2
  have left := read_index _ ((catalog f).2 hf)
  have right := read_index _ ((catalog g).2 hg)
  constructor
  · intro eq
    change (distinctFacts v.facts).idxOf f = (distinctFacts v.facts).idxOf g at eq
    rw [eq, right] at left
    exact (Option.some.inj left).symm
  · rintro rfl
    rfl

private def disclosureContent (facts : List Content) (relations : List (Atom Nat)) : Content :=
  ExtTreeSet.ofList (facts.flatMap ExtTreeSet.toList ++ relations)

def Disclosure.content {W : Type} (v : Disclosure Content W) := disclosureContent v.facts v.assertions

def SharedDisclosure.content {W : Type} (s : SharedDisclosure W) := disclosureContent s.table s.layout.assertions

/-- Утверждение 6.3. Каждый полный факт предъявлен один раз. Чтение всех
позиций восстанавливает исходное дерево со всеми свидетельствами.
Вычисление содержания непосредственно по общей таблице даёт прежние атомы. -/
theorem share_preserves {W : Type} (v : Disclosure Content W) :
    (share v).table.Nodup ∧ (share v).restore = some v ∧ (share v).content = v.content := by
  obtain ⟨unique, members⟩ := distinct_spec v.facts
  refine ⟨unique, v.read_map (fun k hk => read_index _ ((members k).2 hk)), ?_⟩
  apply ExtTreeSet.ext_mem
  intro a
  simp [share, SharedDisclosure.content, Disclosure.content, disclosureContent,
    Disclosure.assertions_map, members]

/-- После П2 сравниваем предъявления по их полному содержанию в одном
состоянии. Разным позициям разрешены разные полные формы одного факта. -/
theorem share_full_presentations {K W : Type} (v : Disclosure K W) (resolve : Resolver)
    (form : K → Form) (denotes : K → Content)
    (full : ∀ k ∈ v.facts, (form k).Full resolve (denotes k)) :
    share ((v.mapFacts form).mapFacts (fun text => text.content resolve)) = share (v.mapFacts denotes) := by
  apply congrArg share
  induction v with
  | fact k => exact congrArg Disclosure.fact (full k List.mem_cons_self).2
  | assertion => rfl
  | atSlot w part ih => exact congrArg (Disclosure.atSlot w) (ih full)
  | both x y ix iy =>
    simp only [Disclosure.mapFacts, ix (fun k hk => full k (List.mem_append_left _ hk)),
      iy (fun k hk => full k (List.mem_append_right _ hk))]

namespace Examples

open Section05.Example

/-- Используем исходные свидетельства §5.3. У каждого есть свой родитель,
адресат, адрес записи, роль и вид вхождения. -/
private abbrev Use := (p : Content) × (c : Content) × Occurrence registry p c
private abbrev View := Disclosure Content Use

private def inB1 (i : Fin b1.inclusions.length) : Use :=
  ⟨b1.content, _, .earlier (.earlier (.earlier (.latest (entry := b1) i)))⟩
private def inB2 (i : Fin b2.inclusions.length) : Use :=
  ⟨b2.content, _, .earlier (.earlier (.latest (entry := b2) i))⟩
private def inA1 (i : Fin a1.inclusions.length) : Use :=
  ⟨a1.content, _, .earlier (.latest (entry := a1) i)⟩
private def inA2 (i : Fin a2.inclusions.length) : Use :=
  ⟨a2.content, _, .latest (entry := a2) i⟩

private def withRelations {names history} (entry : Entry names history) (parts : View) : View :=
  entry.own.foldr (fun a rest => .both (.assertion (Entry.resolveAtom history a)) rest) parts

private def leafUse (w : Use) : View := .atSlot w (.fact w.2.1)

private def firstBlock := withRelations b1 (.both
  (leafUse (inB1 ⟨0, by decide⟩)) (leafUse (inB1 ⟨1, by decide⟩)))
private def secondBlock := withRelations b2 (.both
  (leafUse (inB2 ⟨0, by decide⟩)) (leafUse (inB2 ⟨1, by decide⟩)))

private def first := withRelations a1 (.both
  (.atSlot (inA1 ⟨0, by decide⟩) firstBlock) (.atSlot (inA1 ⟨1, by decide⟩) secondBlock))
private def second := withRelations a2 (.both
  (leafUse (inA2 ⟨0, by decide⟩)) (.atSlot (inA2 ⟨1, by decide⟩) secondBlock))

/-- Адреса и роли по пути от корня до каждой позиции участия, читающей
данный номер в таблице. Концы путей могут совпадать. -/
private def pathsTo (slot : Nat) : Disclosure Nat Use → List (List (Nat × Nat × String))
  | .fact i => if i = slot then [[]] else []
  | .assertion _ => []
  | .both x y => pathsTo slot x ++ pathsTo slot y
  | .atSlot use part =>
    let w := use.2.2
    (pathsTo slot part).map ((w.address.1, w.address.2, w.roleAndKind.1) :: ·)

/-- A1: C2 один раз в таблице, а пути через B1 и B2 имеют исходные роли.
ρ по-прежнему принимает id(B1), id(B2), вычисленные в реестре. -/
theorem shared_in_two_parents :
    (share first).table = [c1.content, c2.content, c3.content] ∧
    pathsTo 1 (share first).layout =
      [[(5,0,"JointAccount.left"), (3,1,"When.right")],
       [(5,1,"JointAccount.right"), (4,0,"While.left")]] ∧
    rho ∈ (share first).layout.assertions ∧ (share first).content = a1.content := by
  exact ⟨by decide, by decide, by decide, (share_preserves first).2.2.trans (by decide)⟩

/-- A2: у того же C2 различимы прямое участие в σ и вложенное участие
через B2. Внешний атом связывает целый B2 с событием e₂. -/
theorem direct_and_nested :
    (share second).table = [c2.content, c3.content] ∧
    pathsTo 0 (share second).layout =
      [[(6,0,"event source")], [(6,1,"whole block"), (4,0,"While.left")]] ∧
    sigma ∈ (share second).layout.assertions ∧ (share second).content = a2.content := by
  exact ⟨by decide, by decide, by decide, (share_preserves second).2.2.trans (by decide)⟩

/-- Связь с исходными предъявлениями §5.3 при любом порядке раскрытия. -/
theorem equivalent_after_expansion :
    (∀ v, Edits (fun a b => b ∈ next a) firstRoot v → v.Full resolve (share first).content) ∧
    (∀ v, Edits (fun a b => b ∈ next a) secondRoot v → v.Full resolve (share second).content) := by
  rw [shared_in_two_parents.2.2.2.trans root_contents.1, direct_and_nested.2.2.2.trans root_contents.2.2.1]
  exact both_root_invariants

end Examples

#print axioms same_slot_iff
#print axioms share_preserves
#print axioms share_full_presentations
#print axioms Examples.equivalent_after_expansion
#print axioms Examples.shared_in_two_parents
#print axioms Examples.direct_and_nested

end SemanticChains.Section06
