import SemanticChains.Section04.Normalization
import SemanticChains.Section05.Representation

/-! §6.1. Два предъявления одних логических фактов в фиксированном состоянии.
Сравнение выбранного S и сравнение поисковых областей W имеют разные условия. -/
namespace SemanticChains.Section06

open Section04 (Absorptions Normal positions)
open Section03 (growth InW)

private def mapPath {F : Type} {R R' : F → F → Type}
    (map : ∀ {p c}, R p c → R' p c) {p f : F} : Path R p f → Path R' p f
  | .here x => .here x
  | .step edge tail => .step (map edge) (mapPath (map := @map) tail)

/-- Следствие 6.1 для произвольного конечного разбора. Списки исходных
позиций могут иметь разный порядок; сравниваются множества результатов.
Оба остатка характеризуются верхними вершинами первого графа. -/
theorem normalization_iff_same_top {F : Type} {R R' : F → F → Type}
    {initial initial' final final' : List F} {n n' : Nat}
    (vertices : ∀ f, f ∈ initial ↔ f ∈ initial')
    (forward : ∀ {p c}, R p c → R' p c) (backward : ∀ {p c}, R' p c → R p c)
    (sources : ∀ {p c}, R p c → p ∈ initial)
    (acyclic : ∀ {p c}, R p c → ¬ Nonempty (Path R c p))
    (steps : Absorptions R n initial final) (done : Normal R final)
    (steps' : Absorptions R' n' initial' final') (done' : Normal R' final') (f : F) :
    let top := f ∈ initial ∧ ∀ p, ¬ Nonempty (R p f)
    (f ∈ final ↔ top) ∧ (f ∈ final' ↔ top) := by
  have sources' {p c} (edge : R' p c) := (vertices p).1 (sources (backward edge))
  have acyclic' {p c} (edge : R' p c) : ¬ Nonempty (Path R' c p) :=
    fun ⟨path⟩ => acyclic (backward edge) ⟨mapPath (map := @backward) path⟩
  refine ⟨Section04.normal_iff_top steps done sources acyclic f, ?_⟩
  rw [Section04.normal_iff_top steps' done' sources' acyclic', ← vertices]
  apply and_congr_right
  intro _
  constructor
  · exact fun h p ⟨edge⟩ => h p ⟨forward edge⟩
  · exact fun h p ⟨edge⟩ => h p ⟨backward edge⟩

section Selected

variable {T : LemmaOne.State} {F I : Type} {M N : ChainModel T F I}
    {E : Expansion M} {D : Expansion N}

/-- Соответствие относится только к конкретным вхождениям в S.
Пара (родитель, подфакт) фиксирована типом свидетеля. Обратимость различает
повторные вхождения, даже когда они связывают одни и те же вершины. -/
structure Rewording (E : Expansion M) (D : Expansion N) where
  root : E.root = D.root
  content : ∀ f, E.InS f → M.factContent f = N.factContent f
  forward : ∀ {p c}, E.AnswerEdge p c → D.AnswerEdge p c
  backward : ∀ {p c}, D.AnswerEdge p c → E.AnswerEdge p c
  recoverOld : ∀ {p c} (e : E.AnswerEdge p c), backward (forward e) = e
  recoverNew : ∀ {p c} (e : D.AnswerEdge p c), forward (backward e) = e
  role : ∀ {p c} (e : E.AnswerEdge p c),
    (N.graph.record (D.toContractEdge (forward e)).val).role =
    (M.graph.record (E.toContractEdge e).val).role
  kind : ∀ {p c} (e : E.AnswerEdge p c),
    (N.graph.record (D.toContractEdge (forward e)).val).kind =
    (M.graph.record (E.toContractEdge e).val).kind

/-- У нового вхождения могут измениться текст и адрес. Чтение в новом
полном тексте подтверждает прежний адресат, вид вхождения и роль. -/
theorem Rewording.read_at_new_address (h : Rewording E D) {p c} (e : E.AnswerEdge p c) :
    let old := M.graph.record (E.toContractEdge e).val
    let new := N.graph.record (D.toContractEdge (h.forward e)).val
    N.presentation.Full p new.parentText ∧
      N.graph.readAt p new.parentText new.address = some (old.kind, old.role, c) := by
  refine ⟨N.graph.parentFull _, ?_⟩
  simpa only [h.role, h.kind] using N.graph.atAddress (D.toContractEdge (h.forward e)).val

/-- Принадлежность S выводится переносом засвидетельствованных путей. -/
theorem Rewording.mem_iff (h : Rewording E D) (f : F) : E.InS f ↔ D.InS f := by
  rw [← E.reachable_iff_mem, ← D.reachable_iff_mem, ← h.root]
  exact ⟨fun ⟨path⟩ => ⟨mapPath (map := @h.forward) path⟩,
    fun ⟨path⟩ => ⟨mapPath (map := @h.backward) path⟩⟩

theorem Rewording.top_iff (h : Rewording E D) (f : F) : E.IsTop f ↔ D.IsTop f := by
  unfold Expansion.IsTop
  rw [h.mem_iff f]
  apply and_congr_right
  intro _
  exact ⟨fun old p ⟨w⟩ => old p ⟨h.backward w⟩, fun new p ⟨w⟩ => new p ⟨h.forward w⟩⟩

/-- Полные тексты могут иметь разную форму и длину. При заданном
соответствии фактов они предъявляют одно и то же полное содержание. -/
theorem Rewording.full_text_content (h : Rewording E D) {f : F} (selected : E.InS f)
    {old new : Reading T} (oldFull : M.presentation.Full f old) (newFull : N.presentation.Full f new) :
    old.textContent = new.textContent :=
  (M.full_content oldFull).trans ((h.content f selected).trans (N.full_content newFull).symm)

/-- Для используемой отсылки к объекту сопоставляются разрешение и роль
по прежнему и новому адресу указания в вопросе (§2.2). Оба чтения
связаны с проверенным представлением того же f. -/
theorem object_at_matched_addresses {Q Q' : String} {e e' : T.Occ} {f : F}
    (old : Section02.ObjectMatch M Q e f) (new : Section02.ObjectMatch N Q' e' f)
    (resolved : T.resolve e = T.resolve e') (role : T.questionRole Q e = T.questionRole Q' e') :
    old.object = new.object ∧ old.role = new.role :=
  ⟨Option.some.inj (old.resolved.symm.trans (resolved.trans new.resolved)),
   Option.some.inj (old.mentioned.symm.trans (role.trans new.mentioned))⟩

/-- Для двух предъявлений выбранного разбора оба результата равны [r].
Каждая полная последовательность поглощений выбирается независимо. -/
theorem Rewording.normal_forms (h : Rewording E D)
    (hr : E.root ∈ M.registered) (hr' : D.root ∈ N.registered)
    {n n' : Nat} {final final' : List F}
    (steps : Absorptions E.AnswerEdge n (positions E) final) (done : Normal E.AnswerEdge final)
    (steps' : Absorptions D.AnswerEdge n' (positions D) final') (done' : Normal D.AnswerEdge final') :
    final = [E.root] ∧ final' = [E.root] := by
  exact ⟨Section04.normalized_eq_singleton E hr steps done,
    (Section04.normalized_eq_singleton D hr' steps' done').trans (congrArg (fun f => [f]) h.root.symm)⟩

end Selected

section Search

variable {T U : LemmaOne.State} {F G I J : Type} {M : ChainModel T F I} {N : ChainModel U G J}

/-- Условия переноса поиска в одну сторону. Сопоставляются начальные
зарегистрированные факты. Продолжение требуется только у уже достижимой
пары и проверяется отдельно для входящих и исходящих рёбер. -/
structure SearchLift (M : ChainModel T F I) (N : ChainModel U G J)
    (seeds : List F) (seeds' : List G) (matchesFact : F → G → Prop) : Prop where
  seed : ∀ x ∈ seeds, x ∈ M.registered → ∃ y ∈ seeds', y ∈ N.registered ∧ matchesFact x y
  children : ∀ {x x' y}, InW M seeds x → InW N seeds' x' → matchesFact x x' →
    M.graph.Edge x y → ∃ y', matchesFact y y' ∧ Nonempty (N.graph.Edge x' y')
  parents : ∀ {x x' y}, InW M seeds x → InW N seeds' x' → matchesFact x x' →
    M.graph.Edge y x → ∃ y', matchesFact y y' ∧ Nonempty (N.graph.Edge y' x')

/-- Каждый достигнутый за n шагов факт имеет соответствующий факт,
достигнутый за те же n шагов во втором предъявлении. -/
theorem SearchLift.stage {seeds seeds' rel} (h : SearchLift M N seeds seeds' rel) (n : Nat) :
    ∀ x ∈ growth M seeds n, ∃ x' ∈ growth N seeds' n, rel x x' := by
  induction n with
  | zero =>
    intro x hit
    obtain ⟨registered, seed⟩ := (Section03.mem_lookup M _ x).1 hit
    obtain ⟨y, seed', reg', matched⟩ := h.seed x seed registered
    exact ⟨y, (Section03.mem_lookup N _ y).2 ⟨reg', seed'⟩, matched⟩
  | succ n ih =>
    intro y hit
    rcases (Section03.mem_growth_succ M).1 hit with old | ⟨x, hx, ⟨edge | edge⟩⟩
    · obtain ⟨y', hy', related⟩ := ih y old
      exact ⟨y', (Section03.mem_growth_succ N).2 (Or.inl hy'), related⟩
    · obtain ⟨x', hx', related⟩ := ih x hx
      obtain ⟨y', matchY, ⟨e'⟩⟩ := h.children ⟨n, hx⟩ ⟨n, hx'⟩ related edge
      exact ⟨y', (Section03.mem_growth_succ N).2 (Or.inr ⟨x', hx', ⟨.inl e'⟩⟩), matchY⟩
    · obtain ⟨x', hx', related⟩ := ih x hx
      obtain ⟨y', matchY, ⟨e'⟩⟩ := h.parents ⟨n, hx⟩ ⟨n, hx'⟩ related edge
      exact ⟨y', (Section03.mem_growth_succ N).2 (Or.inr ⟨x', hx', ⟨.inr e'⟩⟩), matchY⟩

/-- Совпадение W по взаимно однозначному соответствию используемых фактов.
Факты вне достижимых компонент могут иметь другие связи. -/
theorem growth_corresponds {seeds seeds' rel} (forward : SearchLift M N seeds seeds' rel)
    (backward : SearchLift N M seeds' seeds (fun y x => rel x y))
    (uniqueRight : ∀ {x y z}, rel x y → rel x z → y = z)
    (uniqueLeft : ∀ {x y z}, rel x z → rel y z → x = y)
    {x y} (matched : rel x y) :
    (∀ n, x ∈ growth M seeds n ↔ y ∈ growth N seeds' n) ∧
      (InW M seeds x ↔ InW N seeds' y) := by
  have stage (n : Nat) : x ∈ growth M seeds n ↔ y ∈ growth N seeds' n := by
    constructor
    · intro hx
      obtain ⟨z, hz, r⟩ := forward.stage n x hx
      exact uniqueRight r matched ▸ hz
    · intro hy
      obtain ⟨z, hz, r⟩ := backward.stage n y hy
      exact uniqueLeft r matched ▸ hz
  exact ⟨stage, ⟨fun ⟨n, hx⟩ => ⟨n, (stage n).1 hx⟩, fun ⟨n, hy⟩ => ⟨n, (stage n).2 hy⟩⟩⟩

end Search

section Example
open Section05
attribute [local instance] lexOrd

/-- Перечень двух действий и утверждение об их порядке обосновывают один
ответ «какие два действия?», но отличаются атомом Before. -/
theorem same_answer_distinct_content :
    ∃ actions ordered : Section05.Content, actions ≠ ordered ∧
      (∀ I, Section05.Holds I ordered → Section05.Holds I actions) ∧
      ∃ I, Section05.Holds I actions ∧ ¬ Section05.Holds I ordered := by
  let cook : Atom Nat := ("Cook", [.event 1, .object 1])
  let setTable : Atom Nat := ("SetTable", [.event 2, .object 1])
  let before : Atom Nat := ("Before", [.event 1, .event 2])
  let actions : Section05.Content := Std.ExtTreeSet.ofList [cook, setTable]
  let ordered : Section05.Content := Std.ExtTreeSet.ofList [cook, setTable, before]
  have absent : before ∉ actions := by decide +revert
  have present : before ∈ ordered := by decide +revert
  refine ⟨actions, ordered, fun eq => absent (eq ▸ present), ?_, ?_⟩
  · intro I
    apply Section05.entails_of_preserves
    intro atom hit
    simp [actions] at hit
    simp [ordered]
    grind
  · exact ⟨fun atom => atom ≠ before, fun _ ha eq => absent (eq ▸ ha), fun h => h before present rfl⟩

end Example

#print axioms normalization_iff_same_top
#print axioms Rewording.read_at_new_address
#print axioms Rewording.normal_forms
#print axioms same_answer_distinct_content
#print axioms growth_corresponds

end SemanticChains.Section06
