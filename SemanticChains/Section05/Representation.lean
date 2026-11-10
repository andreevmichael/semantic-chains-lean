import SemanticChains.Section05.Registry
import SemanticChains.Section04.SingleLink

/-! §5.2. Конечные представления в одном фиксированном положительном реестре. -/
namespace SemanticChains.Section05

open Std
attribute [local instance] lexOrd

inductive Leaf where
  | atom (a : Atom Nat)
  | ref (name : String)
  deriving DecidableEq, Repr

/-- Двоичное and представляет любую непустую конечную последовательность частей. -/
inductive Form where
  | leaf (l : Leaf)
  | both (left right : Form)
  deriving DecidableEq, Repr

def Form.leaves : Form → List Leaf
  | .leaf l => [l]
  | .both l r => l.leaves ++ r.leaves

abbrev Resolver := String → Option Content

def Leaf.atoms (resolve : Resolver) : Leaf → List (Atom Nat)
  | .atom a => [a]
  | .ref name => (resolve name).toList.flatMap ExtTreeSet.toList

def Form.content (v : Form) (resolve : Resolver) : Content :=
  ExtTreeSet.ofList (v.leaves.flatMap (Leaf.atoms resolve))

def Form.Valid (v : Form) (resolve : Resolver) : Prop :=
  ∀ n, Leaf.ref n ∈ v.leaves → ∃ f, resolve n = some f

def Form.Full (v : Form) (resolve : Resolver) (f : Content) : Prop :=
  v.Valid resolve ∧ v.content resolve = f

/-- Явный атом предъявляет объекты в своих аргументах. Для одного лишь
имени факта нельзя засчитать обозначения внутри содержания адресата. -/
def Form.Designates (v : Form) (o : Nat) : Prop :=
  ∃ a, Leaf.atom a ∈ v.leaves ∧ Argument.object o ∈ a.2

def Holds (I : Atom Nat → Prop) (f : Content) : Prop := ∀ a ∈ f, I a

theorem entails_of_preserves {p c : Content} (incl : Preserves p c) (I : Atom Nat → Prop) :
    Holds I p → Holds I c := fun hp a ha => hp a (incl a ha)

/-- В положительном языке без дополнительных ограничений все записи
совместно выполнимы. При ограничении класса истолкований совместная
выполнимость в этом классе проверяется отдельно. -/
theorem positive_registry_satisfiable (history : List Content) :
    ∃ I : Atom Nat → Prop, ∀ f ∈ history, Holds I f :=
  ⟨fun _ => True, fun _ _ _ _ => trivial⟩

theorem full_meaning {resolve f v} (full : Form.Full v resolve f) (I : Atom Nat → Prop) :
    Holds I (v.content resolve) ↔ Holds I f := full.2 ▸ Iff.rfl

theorem mem_form_content {v : Form} {resolve : Resolver} {a : Atom Nat} :
    a ∈ v.content resolve ↔ ∃ l ∈ v.leaves, a ∈ l.atoms resolve := by
  simp [Form.content]

theorem ref_full {resolve : Resolver} {n f} (read : resolve n = some f) :
    (Form.leaf (.ref n)).Full resolve f := by
  constructor
  · intro name hit
    have eq : name = n := by simpa [Form.leaves] using hit
    exact ⟨f, eq ▸ read⟩
  · apply ExtTreeSet.ext_mem
    intro a
    simp [mem_form_content, Form.leaves, Leaf.atoms, read]

/-- Одно целое подвыражение; адрес внутри аргумента атома здесь невозможен. -/
inductive Context where
  | hole
  | left (inner : Context) (right : Form)
  | right (left : Form) (inner : Context)

def Context.fill : Context → Form → Form
  | .hole, v => v
  | .left inner r, v => .both (inner.fill v) r
  | .right l inner, v => .both l (inner.fill v)

def Context.outside : Context → List Leaf
  | .hole => []
  | .left inner r => inner.outside ++ r.leaves
  | .right l inner => l.leaves ++ inner.outside

theorem Context.leaves_fill (u : Context) (v : Form) (l : Leaf) :
    l ∈ (u.fill v).leaves ↔ l ∈ u.outside ∨ l ∈ v.leaves := by
  induction u with
  | hole => simp [Context.fill, Context.outside]
  | left inner r ih | right r inner ih =>
    simp only [Context.fill, Form.leaves, Context.outside, List.mem_append, ih]
    grind

/-- Формула C_T(U[V]) = B_U ∪ C_T(V), по принадлежности атомов. -/
theorem Context.content_fill (u : Context) (v : Form) (resolve : Resolver) (a : Atom Nat) :
    a ∈ (u.fill v).content resolve ↔
      a ∈ u.outside.flatMap (Leaf.atoms resolve) ∨ a ∈ v.content resolve := by
  simp only [mem_form_content, u.leaves_fill, List.mem_flatMap]
  grind

theorem Context.designates_fill (u : Context) (v : Form) (o : Nat) :
    (u.fill v).Designates o ↔
      (∃ a, Leaf.atom a ∈ u.outside ∧ Argument.object o ∈ a.2) ∨ v.Designates o := by
  simp only [Form.Designates, u.leaves_fill]
  grind

/-- Лемма 5.2: замена по выбранному адресу сохраняет полноту родителя.
Все ссылки вне этого места читаются по прежнему реестру. -/
theorem local_expansion {resolve : Resolver} {name : String} {p f : Content}
    (u : Context) (read : resolve name = some f) (v : Form) (child : v.Full resolve f)
    (parent : (u.fill (.leaf (.ref name))).Full resolve p) :
    (u.fill v).Full resolve p := by
  constructor
  · intro n h
    rcases (u.leaves_fill v _).1 h with outside | inside
    · exact parent.1 n ((u.leaves_fill _ _).2 (Or.inl outside))
    · exact child.1 n inside
  · apply Eq.trans _ parent.2
    apply ExtTreeSet.ext_mem
    intro a
    rw [u.content_fill, u.content_fill, child.2, (ref_full read).2]

def Form.combine (v : Form) : List Form → Form
  | [] => v
  | w :: ws => .both v (w.combine ws)

theorem Form.leaves_combine (v : Form) (vs : List Form) :
    (v.combine vs).leaves = v.leaves ++ vs.flatMap Form.leaves := by
  induction vs generalizing v with
  | nil => simp [Form.combine]
  | cons w ws ih => simp [Form.combine, Form.leaves, ih]

/-- У каждого зарегистрированного факта есть представление из всех его
явных атомов, предъявляющее каждый объект, указанный в их аргументах. -/
theorem explicit_representation (resolve : Resolver) {f : Content} (nonempty : f ≠ ∅) :
    ∃ v : Form, v.Full resolve f ∧ ∀ a ∈ f, Leaf.atom a ∈ v.leaves := by
  cases atoms : f.toList with
  | nil => exact False.elim (nonempty (ExtTreeSet.toList_eq_nil_iff.mp atoms))
  | cons a rest =>
    let v := (Form.leaf (.atom a)).combine (rest.map (fun b => Form.leaf (.atom b)))
    have leaves : v.leaves = f.toList.map Leaf.atom := by
      simp [v, Form.leaves_combine, Form.leaves, atoms, List.flatMap_map]
      clear v atoms nonempty
      induction rest with
      | nil => rfl
      | cons x xs ih => simp [ih]
    refine ⟨v, ⟨?_, ?_⟩, ?_⟩
    · intro name h
      simp [leaves] at h
    · apply ExtTreeSet.ext_mem
      intro b
      rw [mem_form_content]
      constructor
      · rintro ⟨l, hl, hb⟩
        rw [leaves] at hl
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
        have eq : b = x := List.mem_singleton.mp hb
        exact eq ▸ ExtTreeSet.mem_toList.mp hx
      · intro hb
        exact ⟨.atom b, leaves ▸ List.mem_map.mpr ⟨b, ExtTreeSet.mem_toList.mpr hb, rfl⟩,
          List.mem_cons_self⟩
    · intro b hb
      simp [leaves, ExtTreeSet.mem_toList, hb]

/-- В списке частей сохраняется конкретное вхождение, включая адрес и роль.
Две позиции с одинаковым адресатом могут иметь разные свидетельства. -/
structure Part {names history} (reg : Registry names history) (p : Content) where
  child : Content
  occurrence : Occurrence reg p child
  form : Form

theorem joint_presentation {names history} {reg : Registry names history} {p : Content}
    {resolve : Resolver} {base : Form} (parent : base.Full resolve p) (parts : List (Part reg p))
    (full : ∀ part ∈ parts, part.form.Full resolve part.child) :
    (base.combine (parts.map Part.form)).Full resolve p ∧
    ∀ part ∈ parts, ∀ o, part.form.Designates o → (base.combine (parts.map Part.form)).Designates o := by
  let joined := base.combine (parts.map Part.form)
  have leaves (l : Leaf) : l ∈ joined.leaves ↔
      l ∈ base.leaves ∨ ∃ part ∈ parts, l ∈ part.form.leaves := by
    simp [joined, Form.leaves_combine, List.flatMap_map]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro n hit
    rcases (leaves _).1 hit with old | ⟨part, mem, inside⟩
    · exact parent.1 n old
    · exact (full part mem).1 n inside
  · apply ExtTreeSet.ext_mem
    intro a
    constructor
    · intro ha
      obtain ⟨l, h, atom⟩ := mem_form_content.mp ha
      rcases (leaves l).1 h with old | ⟨part, mem, inside⟩
      · exact parent.2 ▸ mem_form_content.mpr ⟨l, old, atom⟩
      · have hc := (full part mem).2 ▸ (mem_form_content.mpr ⟨l, inside, atom⟩ :
            a ∈ part.form.content resolve)
        exact occurrence_preserves part.occurrence a hc
    · intro ha
      obtain ⟨l, h, atom⟩ := mem_form_content.mp (parent.2 ▸ ha : a ∈ base.content resolve)
      exact mem_form_content.mpr ⟨l, (leaves _).2 (Or.inl h), atom⟩
  · intro part mem o key
    obtain ⟨a, h, arg⟩ := key
    exact ⟨a, (leaves _).2 (Or.inr ⟨part, mem, h⟩), arg⟩

/-- Интерфейс однозначных словесных шаблонов статьи: чтение напечатанной
конструкции восстанавливает тот же символ, аргументы, имена и скобки. -/
structure Templates where
  print : Form → String
  read : String → Option Form
  roundtrip : ∀ v, read (print v) = some v

private def Target.leaves {names} {history : List Content} (t : Target names (List.length history)) : List Leaf :=
  match t with
  | .included i => (history.get i).toList.map Leaf.atom
  | .reference name _ _ => [.ref name]

private def outsideContext (before after : List Leaf) : Context :=
  before.foldr (fun l u => .right (.leaf l) u)
    (after.foldl (fun u l => .left u (.leaf l)) .hole)

private theorem outside_sequence (before after : List Leaf) :
    (outsideContext before after).outside = before ++ after := by
  have suffixLeaves (u : Context) (xs : List Leaf) :
      (xs.foldl (fun ctx l => Context.left ctx (.leaf l)) u).outside = u.outside ++ xs := by
    induction xs generalizing u with
    | nil => simp
    | cons head tail ih => simp [ih, Context.outside, Form.leaves, List.append_assoc]
  induction before with
  | nil => simp [outsideContext, suffixLeaves, Context.outside]
  | cons head tail ih => simpa [outsideContext, Context.outside, Form.leaves] using ih

private def ExtendsNames (resolve : Resolver) (names : String → Option Nat) (history : List Content) :=
  ∀ {n f}, resolveFact names history n = some f → resolve n = some f

private theorem earlier_names {resolve names history more} (h : ExtendsNames resolve names (history ++ more)) :
    ExtendsNames resolve names history := by
  intro n f read
  apply h
  cases named : names n with
  | none => simp [resolveFact, named] at read
  | some i =>
    simp only [resolveFact, named, Option.bind_some] at read ⊢
    obtain ⟨lt, eq⟩ := List.getElem?_eq_some_iff.mp read
    exact List.getElem?_eq_some_iff.mpr ⟨by simp; omega, by simpa [List.getElem_append_left lt] using eq⟩

private theorem target_read {resolve names history} (ext : ExtendsNames resolve names history)
    (t : Target names history.length) :
    (∀ n, Leaf.ref n ∈ t.leaves → ∃ f, resolve n = some f) ∧
    (∀ a, (∃ l ∈ t.leaves, a ∈ l.atoms resolve) ↔ a ∈ history.get t.index) := by
  cases t with
  | included i =>
    constructor
    · simp [Target.leaves]
    · intro a
      constructor
      · rintro ⟨l, hl, ha⟩
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
        exact List.mem_singleton.mp ha ▸ ExtTreeSet.mem_toList.mp hx
      · intro ha
        exact ⟨.atom a, List.mem_map.mpr ⟨a, ExtTreeSet.mem_toList.mpr ha, rfl⟩, List.mem_cons_self⟩
  | reference n i resolved =>
    have read := ext (reference_resolves (history := history) resolved)
    constructor
    · intro name hit
      have eq : name = n := by simpa [Target.leaves] using hit
      exact ⟨_, eq ▸ read⟩
    · intro a
      simp [Target.leaves, Target.index, Leaf.atoms, read]

/-- Контекст строится по конкретному номеру вхождения в исходной записи.
Соседние сохраняющие ссылки остаются именованными; у включений без имени
предъявляются атомы адресата. При переходе к старой записи имена стабильны. -/
private theorem occurrence_context {names history} {reg : Registry names history} {p c : Content}
    (w : Occurrence reg p c) (resolve : Resolver) (ext : ExtendsNames resolve names history) :
    ∃ u : Context, ∀ v : Form, v.Full resolve c → (u.fill v).Full resolve p := by
  induction w with
  | earlier _ ih => exact ih (earlier_names ext)
  | @latest h previous entry _ slot =>
    have reads : ExtendsNames resolve names h := earlier_names ext
    let links := entry.inclusions
    let chosen := links.get slot
    let before := links.take slot.val
    let after := links.drop (slot.val + 1)
    have split : links = before ++ chosen :: after := by
      unfold before after chosen
      rw [List.get_eq_getElem, List.getElem_cons_drop slot.isLt, List.take_append_drop]
    let own := (entry.own.map (Entry.resolveAtom h)).map Leaf.atom
    let leavesOf := fun t : String × Target names h.length => t.2.leaves
    let u := outsideContext (own ++ before.flatMap leavesOf) (after.flatMap leavesOf)
    have outside (l : Leaf) : l ∈ u.outside ↔ l ∈ own ∨
        ∃ t ∈ before ++ after, l ∈ t.2.leaves := by
      change l ∈ (outsideContext (own ++ before.flatMap leavesOf) (after.flatMap leavesOf)).outside ↔ _
      rw [outside_sequence]
      simp only [List.mem_append, List.mem_flatMap]
      constructor
      · rintro ((ownLeaf | ⟨t, hb, hl⟩) | ⟨t, ha, hl⟩)
        · exact Or.inl ownLeaf
        · exact Or.inr ⟨t, Or.inl hb, hl⟩
        · exact Or.inr ⟨t, Or.inr ha, hl⟩
      · rintro (ownLeaf | ⟨t, hb | ha, hl⟩)
        · exact Or.inl (Or.inl ownLeaf)
        · exact Or.inl (Or.inr ⟨t, hb, hl⟩)
        · exact Or.inr ⟨t, ha, hl⟩
    refine ⟨u, ?_⟩
    intro v child
    constructor
    · intro n hit
      rcases (u.leaves_fill _ _).1 hit with extLeaf | hv
      · rcases (outside _).1 extLeaf with atom | ⟨t, _, hl⟩
        · simp [own] at atom
        · exact (target_read reads t.2).1 n hl
      · exact child.1 n hv
    · apply ExtTreeSet.ext_mem
      intro a
      rw [u.content_fill, child.2, entry.mem_content]
      change _ ↔ _ ∨ ∃ t ∈ links, a ∈ h.get t.2.index
      rw [split]
      simp only [List.mem_append, List.mem_cons, List.mem_flatMap]
      constructor
      · rintro (⟨l, hl, ha⟩ | ha)
        · rcases (outside l).1 hl with ownLeaf | ⟨t, member, leaf⟩
          · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ownLeaf
            exact Or.inl (List.mem_singleton.mp ha ▸ hb)
          · exact Or.inr ⟨t, (List.mem_append.mp member).imp_right Or.inr,
              (target_read reads t.2).2 a |>.1 ⟨l, leaf, ha⟩⟩
        · exact Or.inr ⟨chosen, Or.inr (Or.inl rfl), ha⟩
      · rintro (ownAtom | ⟨t, member, ha⟩)
        · exact Or.inl ⟨.atom a, (outside _).2 (Or.inl (List.mem_map.mpr ⟨a, ownAtom, rfl⟩)), List.mem_cons_self⟩
        · rcases member with hb | eq | ha'
          · obtain ⟨l, leaf, inside⟩ := ((target_read reads t.2).2 a).2 ha
            exact Or.inl ⟨l, (outside l).2 (Or.inr ⟨t, List.mem_append_left _ hb, leaf⟩), inside⟩
          · subst t
            exact Or.inr ha
          · obtain ⟨l, leaf, inside⟩ := ((target_read reads t.2).2 a).2 ha
            exact Or.inl ⟨l, (outside l).2 (Or.inr ⟨t, List.mem_append_right _ ha', leaf⟩), inside⟩

/-- Конкретные П1–П2 для строк: раскрытие в засвидетельствованном месте
исходного родителя. Единственное требование к шаблонам — обратимость чтения. -/
noncomputable def registryPresentation {names history} (reg : Registry names history)
    (words : Templates) : Presentation Content Nat where
  Occurrence := Occurrence reg
  Full f text := ∃ v, words.read text = some v ∧ v.Full (resolveFact names history) f
  Designates text o := ∃ v, words.read text = some v ∧ v.Designates o
  expand w text :=
    let u := Classical.choose (occurrence_context w (resolveFact names history) (fun h => h))
    match words.read text with
    | some v => words.print (u.fill v)
    | none => text
  full_expand := by
    rintro p c w text ⟨v, read, full⟩
    simp only [read]
    exact ⟨_, words.roundtrip _, Classical.choose_spec (occurrence_context w _ (fun h => h)) v full⟩
  retains_designation := by
    rintro p c w text o _ ⟨v, read, key⟩
    simp only [read]
    let u := Classical.choose (occurrence_context w (resolveFact names history) (fun h => h))
    exact ⟨u.fill v, words.roundtrip _, (u.designates_fill v o).2 (Or.inr key)⟩

/-- П1 для объекта, указанного участником явного атома зарегистрированного
факта. Шаблон даёт конечный текст и проверяемое обозначение этого объекта. -/
theorem registered_object_text {names history} (reg : Registry names history) (words : Templates)
    {f : Content} (registered : f ∈ history) {a : Atom Nat} (atom : a ∈ f)
    {o : Nat} (argument : Argument.object o ∈ a.2) :
    ∃ text, (registryPresentation reg words).Full f text ∧
      (registryPresentation reg words).Designates text o := by
  obtain ⟨v, full, visible⟩ := explicit_representation (resolveFact names history)
    (reg.registered_nonempty f registered)
  exact ⟨words.print v, ⟨v, words.roundtrip _, full⟩, ⟨v, words.roundtrip _, a, visible a atom, argument⟩⟩

theorem registry_path_key {names history} (reg : Registry names history) (words : Templates)
    {r f : Content} (path : Path (Occurrence reg) r f) {v o}
    (full : (registryPresentation reg words).Full f v)
    (key : (registryPresentation reg words).Designates v o) :
    ∃ text, (registryPresentation reg words).Full r text ∧
      (registryPresentation reg words).Designates text o :=
  present_at_root (registryPresentation reg words) path full key

/-- Выбор строгих вхождений, с сохранением отдельных свидетельств. -/
abbrev Selection {names history} (reg : Registry names history) :=
  (p : Content) → List ((c : Content) × Edge reg p c)

/-- На границе остаётся базовое полное представление. Во внутренней вершине
присоединяем представления всех выбранных вхождений в исходном порядке.
Убывание размера из §5.1 завершает построение даже при общих подфактах. -/
def treeForm {names history} {reg : Registry names history} (chosen : Selection reg)
    (base : Content → Form) (p : Content) : Form :=
  (base p).combine ((chosen p).map fun child => treeForm chosen base child.1)
termination_by p.size
decreasing_by exact (edge_strict child.2).2.2

theorem tree_full {names history} {reg : Registry names history} (chosen : Selection reg)
    (base : Content → Form) (full : ∀ f ∈ history, (base f).Full (resolveFact names history) f)
    (p : Content) (registered : p ∈ history) :
    (treeForm chosen base p).Full (resolveFact names history) p := by
  let part (e : (c : Content) × Edge reg p c) : Part reg p :=
    ⟨e.1, e.2.val, treeForm chosen base e.1⟩
  have ok : ∀ t ∈ (chosen p).map part, t.form.Full (resolveFact names history) t.child := by
    intro t ht
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp ht
    exact tree_full chosen base full e.1 e.2.val.endpoints.2
  have assembled := (joint_presentation (full p registered) _ ok).1
  rw [treeForm]
  simpa [part, List.map_map] using assembled
termination_by p.size
decreasing_by exact (edge_strict e.2).2.2

theorem tree_child_key {names history} {reg : Registry names history} (chosen : Selection reg)
    (base : Content → Form) {p o} {child : (c : Content) × Edge reg p c} (selected : child ∈ chosen p)
    (key : (treeForm chosen base child.1).Designates o) : (treeForm chosen base p).Designates o := by
  obtain ⟨a, visible, arg⟩ := key
  refine ⟨a, ?_, arg⟩
  rw [treeForm, Form.leaves_combine, List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨child, selected, rfl⟩, visible⟩)

/-- Явные базовые представления дают такое раскрытие для любого
зарегистрированного корня, без дополнительной предпосылки о базовых текстах. -/
theorem exists_full_tree {names history} (reg : Registry names history) (chosen : Selection reg) :
    ∃ base : Content → Form, ∀ p ∈ history,
      (treeForm chosen base p).Full (resolveFact names history) p ∧
      ∀ a ∈ p, Leaf.atom a ∈ (treeForm chosen base p).leaves := by
  classical
  let explicit (p : Content) (hp : p ∈ history) := explicit_representation (resolveFact names history)
    (reg.registered_nonempty p hp)
  let base (p : Content) := if hp : p ∈ history then Classical.choose (explicit p hp) else .leaf (.ref "")
  have spec (p : Content) (hp : p ∈ history) :
      (base p).Full (resolveFact names history) p ∧ ∀ a ∈ p, Leaf.atom a ∈ (base p).leaves := by
    simpa [base, hp] using Classical.choose_spec (explicit p hp)
  refine ⟨base, fun p hp => ⟨tree_full chosen base (fun f hf => (spec f hf).1) p hp, ?_⟩⟩
  intro a ha
  rw [treeForm, Form.leaves_combine]
  exact List.mem_append_left _ ((spec p hp).2 a ha)

#print axioms exists_full_tree
#print axioms local_expansion
#print axioms joint_presentation
#print axioms registry_path_key
#print axioms tree_full

end SemanticChains.Section05
