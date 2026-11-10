import SemanticChains.Section05.Representation

/-! §5.3. Два примера раскрытия в одном фиксированном положительном реестре. -/
namespace SemanticChains.Section05.Example

open Std
attribute [local instance] lexOrd

private def names : String → Option Nat
  | "C1" => some 0 | "C2" => some 1 | "C3" => some 2
  | "B1" => some 3 | "B2" => some 4 | "A1" => some 5 | "A2" => some 6
  | _ => none

/-- Первые три идентификатора объектов обозначают участников, следующие
три — go_to_bed, cook и sleep. События e₁, e₂, e₃ имеют собственный тип. -/
private def eventAtom {Ref : Type} (event person action : Nat) : Atom Ref :=
  ("Event", [.event event, .object person, .object action])

private def kyle {Ref : Type} : Atom Ref := eventAtom 1 1 4
private def emma {Ref : Type} : Atom Ref := eventAtom 2 2 5
private def child {Ref : Type} : Atom Ref := eventAtom 3 3 6
private def whenAtom {Ref : Type} : Atom Ref := ("When", [.event 1, .event 2])
private def whileAtom {Ref : Type} : Atom Ref := ("While", [.event 2, .event 3])

def c1 : Entry names [] := ⟨[kyle], []⟩
def c2 : Entry names [c1.content] := ⟨[emma], []⟩
def c3 : Entry names [c1.content, c2.content] := ⟨[child], []⟩
private def events := [c1.content, c2.content, c3.content]

def b1 : Entry names events :=
  ⟨[whenAtom], [("When.left", .reference "C1" ⟨0, by decide⟩ rfl),
                 ("When.right", .reference "C2" ⟨1, by decide⟩ rfl)]⟩
def b2 : Entry names (events ++ [b1.content]) :=
  ⟨[whileAtom], [("While.left", .reference "C2" ⟨1, by decide⟩ rfl),
                  ("While.right", .reference "C3" ⟨2, by decide⟩ rfl)]⟩

private def blocks := events ++ [b1.content, b2.content]
private def joint {Ref : Type} (first second : Ref) : Atom Ref :=
  ("JointAccount", [.fact first, .fact second])
private def relates {Ref : Type} (block : Ref) : Atom Ref :=
  ("RelatesBlockToEvent", [.fact block, .event 2])

def a1 : Entry names blocks :=
  ⟨[joint ⟨3, by decide⟩ ⟨4, by decide⟩],
    [("JointAccount.left", .reference "B1" ⟨3, by decide⟩ rfl),
     ("JointAccount.right", .reference "B2" ⟨4, by decide⟩ rfl)]⟩
def a2 : Entry names (blocks ++ [a1.content]) :=
  ⟨[relates ⟨4, by decide⟩],
    [("event source", .reference "C2" ⟨1, by decide⟩ rfl),
     ("whole block", .reference "B2" ⟨4, by decide⟩ rfl)]⟩
private def history := blocks ++ [a1.content, a2.content]
def resolve := resolveFact names history

def registry : Registry names history :=
  let r1 := Registry.add .empty c1 (by decide)
  let r2 := Registry.add r1 c2 (by decide)
  let r3 := Registry.add r2 c3 (by decide)
  let r4 := Registry.add r3 b1 (by decide)
  let r5 := Registry.add r4 b2 (by decide)
  let r6 := Registry.add r5 a1 (by decide)
  Registry.add r6 a2 (by decide)

/-- Один и тот же C2 найден в двух родителях. Свидетельства проверяем
по исходным записям, сохраняя позицию и роль каждого участия. -/
private def b1c2 : Edge registry b1.content c2.content :=
  ⟨.earlier (.earlier (.earlier (.latest (entry := b1) ⟨1, by decide⟩))), by decide⟩
private def b2c2 : Edge registry b2.content c2.content :=
  ⟨.earlier (.earlier (.latest (entry := b2) ⟨0, by decide⟩)), by decide⟩

theorem shared_event_occurrences :
    b1c2.val.address ≠ b2c2.val.address ∧
    b1c2.val.roleAndKind = ("When.right", .reference) ∧
    b2c2.val.roleAndKind = ("While.left", .reference) := by decide

def rho := joint (factId blocks ⟨3, by decide⟩) (factId blocks ⟨4, by decide⟩)
def sigma := relates (factId blocks ⟨4, by decide⟩)
def expectedA1 : Content := ExtTreeSet.ofList [kyle, emma, child, whenAtom, whileAtom, rho]
def expectedA2 : Content := ExtTreeSet.ofList [emma, child, whileAtom, sigma]

theorem root_contents :
    a1.content = expectedA1 ∧ a1.content.size = 6 ∧
    a2.content = expectedA2 ∧ a2.content.size = 4 := by decide

/-- В допустимом положительном истолковании оба родителя истинны, а ρ
ложно. Его добавляет собственное утверждение A1. -/
theorem shared_event_does_not_entail_joint :
    ∃ I, Holds I b1.content ∧ Holds I b2.content ∧ ¬ I rho := by
  refine ⟨fun atom => atom ≠ rho, ?_, ?_, fun h => h rfl⟩
  · intro atom member eq
    exact (by decide : rho ∉ b1.content) (eq ▸ member)
  · intro atom member eq
    exact (by decide : rho ∉ b2.content) (eq ▸ member)

/-- В A1 к C2 приходят через обоих родителей. В A2 доступны прямое
вхождение C2 и путь через B2; вершина назначения у этих путей одна. -/
theorem routes_to_c2 :
    (∃ left : Edge registry a1.content b1.content, ∃ right : Edge registry a1.content b2.content,
      left.val.address ≠ right.val.address ∧
      Nonempty (Path (Edge registry) b1.content c2.content) ∧
      Nonempty (Path (Edge registry) b2.content c2.content)) ∧
    (∃ direct : Edge registry a2.content c2.content, ∃ via : Edge registry a2.content b2.content,
      direct.val.address ≠ via.val.address ∧ Nonempty (Path (Edge registry) b2.content c2.content)) := by
  let left : Edge registry a1.content b1.content :=
    ⟨.earlier (.latest (entry := a1) ⟨0, by decide⟩), by decide⟩
  let right : Edge registry a1.content b2.content :=
    ⟨.earlier (.latest (entry := a1) ⟨1, by decide⟩), by decide⟩
  let direct : Edge registry a2.content c2.content :=
    ⟨.latest (entry := a2) ⟨0, by decide⟩, by decide⟩
  let via : Edge registry a2.content b2.content :=
    ⟨.latest (entry := a2) ⟨1, by decide⟩, by decide⟩
  exact ⟨⟨left, right, by change (5, 0) ≠ ((5, 1) : Nat × Nat); decide, ⟨.step b1c2 (.here _)⟩, ⟨.step b2c2 (.here _)⟩⟩,
         ⟨direct, via, by change (6, 0) ≠ ((6, 1) : Nat × Nat); decide, ⟨.step b2c2 (.here _)⟩⟩⟩

/-- Предполагая установленное обозначение Эммы, можно начать с C2:
явный атом этого факта содержит идентификатор участника в своей роли. -/
theorem emma_as_search_key (words : Templates) :
    ∃ text, (registryPresentation registry words).Full c2.content text ∧
      (registryPresentation registry words).Designates text 2 := by
  exact registered_object_text registry words (a := emma) (by decide) (by decide) (by decide)

private def atom (a : Atom Nat) := Form.leaf (.atom a)
private def ref (n : String) := Form.leaf (.ref n)
private def blockForm (left right : String) (rel : Atom Nat) :=
  (ref left).combine [ref right, atom rel]

def firstRoot := blockForm "B1" "B2" rho
def secondRoot := blockForm "C2" "B2" sigma

private def presentations : List (String × Form) :=
  [("C1", atom kyle), ("C2", atom emma), ("C3", atom child),
   ("B1", blockForm "C1" "C2" whenAtom), ("B2", blockForm "C2" "C3" whileAtom),
   ("A1", firstRoot), ("A2", secondRoot)]

private def forms (name : String) := presentations.lookup name

/-- Один переход раскрывает ровно одну ссылку по адресу; остальные ветви
остаются частью того же контекста. -/
def next : Form → List Form
  | .leaf (.atom _) => []
  | .leaf (.ref n) => (forms n).toList
  | .both l r => ((next l).map (Form.both · r)) ++ ((next r).map (Form.both l ·))

private theorem next_at {v u : Form} (h : u ∈ next v) :
    ∃ site : Context, ∃ name replacement, forms name = some replacement ∧
      v = site.fill (ref name) ∧ u = site.fill replacement := by
  induction v generalizing u with
  | leaf l =>
    cases l with
    | atom => exact False.elim (List.not_mem_nil h)
    | ref n =>
      refine ⟨.hole, n, u, ?_, rfl, rfl⟩
      cases d : forms n <;> simp_all [next]
  | both l r il ir =>
    rcases List.mem_append.mp h with left | right
    · obtain ⟨childForm, hit, rfl⟩ := List.mem_map.mp left
      obtain ⟨site, n, rep, read, eq, eq'⟩ := il hit
      exact ⟨.left site r, n, rep, read, congrArg (Form.both · r) eq, congrArg (Form.both · r) eq'⟩
    · obtain ⟨childForm, hit, rfl⟩ := List.mem_map.mp right
      obtain ⟨site, n, rep, read, eq, eq'⟩ := ir hit
      exact ⟨.right l site, n, rep, read, congrArg (Form.both l ·) eq, congrArg (Form.both l ·) eq'⟩

private theorem next_at_iff (v u : Form) :
    u ∈ next v ↔ ∃ site : Context, ∃ name replacement, forms name = some replacement ∧
      v = site.fill (ref name) ∧ u = site.fill replacement := by
  refine ⟨next_at, ?_⟩
  rintro ⟨site, name, replacement, read, rfl, rfl⟩
  induction site with
  | hole => simp [Context.fill, ref, next, read]
  | left inner right ih =>
    exact List.mem_append_left _ (List.mem_map.mpr ⟨_, ih, rfl⟩)
  | right left inner ih =>
    exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)

private def namesValid (v : Form) := v.leaves.all fun l => match l with
  | .atom _ => true
  | .ref n => (resolve n).isSome

private theorem valid_of_check {v : Form} (valid : namesValid v = true) : v.Valid resolve := by
  intro n hit
  have ok := List.all_eq_true.mp valid (.ref n) hit
  simpa using (Option.isSome_iff_exists.mp (show (resolve n).isSome from ok))

/-- У каждой ссылки замена прочитана именно как полный факт, указанный
в реестре §5.1. Таблица представлений не задаёт содержание фактов. -/
private theorem replacement_full {name v} (read : forms name = some v) :
    ∃ f, resolve name = some f ∧ v.Full resolve f := by
  have checked : presentations.all (fun (n,w) =>
      namesValid w && (resolve n).any (fun f => decide (w.content resolve = f))) = true := by
    decide
  obtain ⟨pre, post, split, _⟩ := List.lookup_eq_some_iff.mp read
  have member : (name,v) ∈ presentations := by rw [split]; simp
  have result := List.all_eq_true.mp checked _ member
  change (namesValid v && (resolve name).any (fun f => decide (v.content resolve = f))) = true at result
  obtain ⟨valid, eq⟩ := Bool.and_eq_true_iff.mp result
  cases found : resolve name with
  | none => simp [found] at eq
  | some f => exact ⟨f, rfl, valid_of_check valid, by simpa [found] using eq⟩

/-- Индукция по произвольной последовательности раскрытий одного адреса.
Каждый шаг использует лемму 5.2 для той же записи и того же состояния. -/
theorem expansion_preserves_root {start final : Form} {f : Content}
    (initial : start.Full resolve f) (steps : Edits (fun v u => u ∈ next v) start final) :
    final.Full resolve f := by
  induction steps with
  | refl => exact initial
  | snoc _ hit ih =>
    obtain ⟨site, name, v, read, rfl, rfl⟩ := (next_at_iff _ _).mp hit
    obtain ⟨childFact, resolved, childFull⟩ := replacement_full read
    exact local_expansion site resolved v childFull ih

theorem both_root_invariants :
    (∀ final, Edits (fun v u => u ∈ next v) firstRoot final → final.Full resolve expectedA1) ∧
    (∀ final, Edits (fun v u => u ∈ next v) secondRoot final → final.Full resolve expectedA2) := by
  constructor
  · exact fun _ => expansion_preserves_root ⟨valid_of_check (by decide), by decide⟩
  · exact fun _ => expansion_preserves_root ⟨valid_of_check (by decide), by decide⟩

/-- Независимая конечная проверка. Собираем уровни до указанной глубины,
затем проверяем замкнутость по всем следующим раскрытиям. -/
private def states (start : Form) : Nat → List Form
  | 0 => [start]
  | n+1 =>
    let seen := states start n
    (seen ++ seen.flatMap next).eraseDups

private def checkStates (start : Form) (f : Content) (depth count transitions : Nat) : Bool :=
  let seen := states start depth
  seen.length == count && (seen.flatMap next).length == transitions &&
  (seen.filter (fun v => (next v).isEmpty)).length == 1 &&
  seen.all (fun v => namesValid v && decide (v.content resolve = f) &&
    (next v).all (fun u => seen.contains u))

#guard checkStates firstRoot expectedA1 6 25 50
#guard checkStates secondRoot expectedA2 4 10 15

#print axioms root_contents
#print axioms routes_to_c2
#print axioms emma_as_search_key
#print axioms shared_event_occurrences
#print axioms shared_event_does_not_entail_joint
#print axioms both_root_invariants

end SemanticChains.Section05.Example
