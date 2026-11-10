import SemanticChains.Section03.Growth

/-! §4.1. Поглощение меняет список самостоятельных позиций.
Все пути и их свидетельства относятся к одному исходному графу. -/

namespace SemanticChains.Section04

variable {F : Type} {R : F → F → Type}

/-- Вершины перечислены без повторов в исходном разборе. Без перестановки
списка удаляем одну позицию y; сохраняющая позиция x остаётся. -/
inductive Absorb (R : F → F → Type) : List F → List F → Prop where
  | remove (pre post : List F) (x y : F) (keep : x ∈ pre ++ post)
      (distinct : x ≠ y) (address : Path R x y) :
      Absorb R (pre ++ y :: post) (pre ++ post)

inductive Absorptions (R : F → F → Type) : Nat → List F → List F → Prop where
  | done (positions : List F) : Absorptions R 0 positions positions
  | step {n before after final} : Absorb R before after → Absorptions R n after final →
      Absorptions R (n + 1) before final

def Normal (R : F → F → Type) (positions : List F) : Prop :=
  ∀ after, ¬ Absorb R positions after

private theorem removable {positions : List F} {x y : F} (hx : x ∈ positions)
    (hy : y ∈ positions) (distinct : x ≠ y) (address : Path R x y) :
    ∃ after, Absorb R positions after := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hy
  have keep : x ∈ pre ++ post := by simpa [List.mem_append, distinct] using hx
  exact ⟨_, .remove pre post x y keep distinct address⟩

theorem Absorb.sublist {before after : List F} (step : Absorb R before after) :
    after.Sublist before := by
  cases step with
  | remove pre post x y keep distinct address =>
    exact (List.Sublist.refl post |>.cons y).append_left pre

theorem Absorb.length_drop {before after : List F} (step : Absorb R before after) :
    after.length + 1 = before.length := by
  cases step
  simp [Nat.add_assoc]

theorem Absorptions.length_balance {n before after} (steps : Absorptions R n before after) :
    after.length + n = before.length := by
  induction steps with
  | done => simp
  | step first _ ih =>
    have h := first.length_drop
    omega

/-- Любой текущий префикс можно довести до полной нормализации. -/
theorem exists_normalization (R : F → F → Type) (positions : List F) :
    ∃ n final, Absorptions R n positions final ∧ Normal R final := by
  classical
  by_cases finished : Normal R positions
  · exact ⟨0, positions, .done _, finished⟩
  · obtain ⟨after, step⟩ : ∃ after, Absorb R positions after := by
      simpa [Normal] using finished
    have smaller : after.length < positions.length := by
      have := step.length_drop
      omega
    obtain ⟨n, final, steps, normal⟩ := exists_normalization R after
    exact ⟨n + 1, final, .step step steps, normal⟩
termination_by positions.length

private theorem Absorb.cover {before after : List F} (step : Absorb R before after)
    {f : F} (original : f ∈ before) : ∃ x ∈ after, Nonempty (Path R x f) := by
  cases step with
  | remove pre post x y keep distinct address =>
    by_cases removed : f = y
    · subst f
      exact ⟨x, keep, ⟨address⟩⟩
    · exact ⟨f, by simpa [List.mem_append, removed] using original, ⟨.here f⟩⟩

/-- Лемма 4.1.1. Из оставшейся позиции к каждому исходному факту ведёт
адрес в исходном графе. К этому префиксу можно приписать любой исходный
адрес внутри факта, сохраняя каждое конкретное вхождение в его суффиксе. -/
theorem Absorptions.cover {n before after} (steps : Absorptions R n before after)
    {f : F} (original : f ∈ before) : ∃ x ∈ after, Nonempty (Path R x f) := by
  induction steps generalizing f with
  | done => exact ⟨f, original, ⟨.here f⟩⟩
  | step first _ ih =>
    obtain ⟨y, keep, ⟨suffix⟩⟩ := first.cover original
    obtain ⟨x, last, ⟨prefixPath⟩⟩ := ih keep
    exact ⟨x, last, ⟨prefixPath.append suffix⟩⟩

theorem Absorptions.step_bound {n before after} (steps : Absorptions R n before after)
    (nonempty : before ≠ []) : n ≤ before.length - 1 := by
  obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil before nonempty
  obtain ⟨x, hx, _⟩ := steps.cover hf
  have pos := List.length_pos_of_mem hx
  have balance := steps.length_balance
  omega

private theorem Absorptions.sublist {n before after} (steps : Absorptions R n before after) :
    after.Sublist before := by
  induction steps with
  | done => exact List.Sublist.refl _
  | step first _ ih => exact ih.trans first.sublist

private theorem path_to_source {x y : F} (path : Path R x y)
    (top : ∀ p, ¬ Nonempty (R p y)) : x = y := by
  induction path with
  | here => rfl
  | step edge _ ih =>
    cases ih top
    exact False.elim (top _ ⟨edge⟩)

/-- Лемма 4.1.2. Источники рёбер принадлежат исходному графу, и ни после
одного ребра нельзя вернуться к его началу. Если в оставшийся y входит ребро p → y,
лемма 4.1.1 даёт оставшийся x с путём к p. Тогда x мог бы поглотить y:
равенство x = y замкнуло бы цикл. -/
theorem normal_iff_top {n initial final} (steps : Absorptions R n initial final)
    (normal : Normal R final) (sources : ∀ {p c}, R p c → p ∈ initial)
    (acyclic : ∀ {p c}, R p c → ¬ Nonempty (Path R c p)) (y : F) :
    y ∈ final ↔ y ∈ initial ∧ ∀ p, ¬ Nonempty (R p y) := by
  constructor
  · intro hy
    refine ⟨steps.sublist.subset hy, ?_⟩
    rintro p ⟨edge⟩
    obtain ⟨x, hx, ⟨toParent⟩⟩ := steps.cover (sources edge)
    have distinct : x ≠ y := by
      rintro rfl
      exact acyclic edge ⟨toParent⟩
    obtain ⟨after, step⟩ := removable hx hy distinct (toParent.append (.step edge (.here y)))
    exact normal after step
  · rintro ⟨original, top⟩
    obtain ⟨x, hx, ⟨address⟩⟩ := steps.cover original
    exact path_to_source address top ▸ hx

/-- Критерий единственной позиции при полной нормализации. -/
theorem singleton_iff_reaches_all {n initial final} (steps : Absorptions R n initial final)
    (normal : Normal R final) (sources : ∀ {p c}, R p c → p ∈ initial)
    (acyclic : ∀ {p c}, R p c → ¬ Nonempty (Path R c p)) (r : F) :
    (∀ y, y ∈ final ↔ y = r) ↔
      r ∈ initial ∧ ∀ f ∈ initial, Nonempty (Path R r f) := by
  constructor
  · intro single
    refine ⟨steps.sublist.subset ((single r).2 rfl), ?_⟩
    intro f hf
    obtain ⟨x, hx, address⟩ := steps.cover hf
    exact (single x).1 hx ▸ address
  · rintro ⟨hr, all⟩
    have eq {y} (hy : y ∈ final) : y = r := by
      obtain ⟨original, top⟩ := (normal_iff_top steps normal sources acyclic y).1 hy
      obtain ⟨path⟩ := all y original
      exact (path_to_source path top).symm
    intro y
    refine ⟨eq, ?_⟩
    rintro rfl
    obtain ⟨x, hx, _⟩ := steps.cover hr
    exact eq hx ▸ hx

section Selected

variable {T : LemmaOne.State} {Fact I : Type} {M : ChainModel T Fact I} (E : Expansion M)

/-- M₀ перечисляет каждую вершину выбранного разбора один раз. -/
noncomputable def positions : List Fact := Section03.lookup M E.InS

theorem mem_positions (hr : E.root ∈ M.registered) (f : Fact) :
    f ∈ positions E ↔ E.InS f := by
  rw [positions, Section03.mem_lookup]
  exact ⟨And.right, fun h => ⟨E.subset_contract hr h, h⟩⟩

private def toContractPath {p f : Fact} : Path E.AnswerEdge p f → Path M.graph.Edge p f
  | .here x => .here x
  | .step w tail => .step (E.toContractEdge w) (toContractPath tail)

/-- Для каждого конкретного вхождения сохраняется доступ к родителю и
чтение именно этого вхождения по его исходному адресу, виду и роли. -/
theorem retained_occurrence (hr : E.root ∈ M.registered) {n final}
    (steps : Absorptions E.AnswerEdge n (positions E) final) {p c : Fact} (edge : E.AnswerEdge p c) :
    let w := (E.toContractEdge edge).val
    let entry := M.graph.record w
    ∃ x ∈ final, Nonempty (Path E.AnswerEdge x p) ∧
      M.graph.readAt p entry.parentText entry.address = some (entry.kind, entry.role, c) := by
  obtain ⟨x, hx, address⟩ := steps.cover ((mem_positions E hr p).2 edge.property)
  exact ⟨x, hx, address, M.graph.atAddress _⟩

/-- Если исходные позиции обосновывают Â, то и после любого числа шагов
оставшиеся позиции обосновывают то же содержание в том же состоянии. -/
theorem absorption_preserves_answer {n final} (steps : Absorptions E.AnswerEdge n (positions E) final)
    {a : T.Content} (justified : ∀ i, (∀ f ∈ positions E, M.holds (M.factContent f) i) →
      M.holds a i) :
    ∀ i, (∀ x ∈ final, M.holds (M.factContent x) i) → M.holds a i := by
  intro i holds
  apply justified i
  intro f original
  obtain ⟨x, hx, ⟨address⟩⟩ := steps.cover original
  exact Section02.path_entails (toContractPath E address) i (holds x hx)

/-- Для Γ_S верхняя вершина единственна по §2.3. -/
theorem normalized_iff_root (hr : E.root ∈ M.registered) {n final}
    (steps : Absorptions E.AnswerEdge n (positions E) final) (normal : Normal E.AnswerEdge final)
    (y : Fact) : y ∈ final ↔ y = E.root := by
  have sources {p c} (edge : E.AnswerEdge p c) := (mem_positions E hr p).2 edge.property
  have acyclic {p c} (edge : E.AnswerEdge p c) : ¬ Nonempty (Path E.AnswerEdge c p) := by
    rintro ⟨back⟩
    exact Section02.no_return (E.toContractEdge edge) ⟨toContractPath E back⟩
  rw [normal_iff_top steps normal sources acyclic, mem_positions E hr]
  exact E.top_iff_root

/-- В списке результата корень встречается ровно один раз. -/
theorem normalized_eq_singleton (hr : E.root ∈ M.registered) {n final}
    (steps : Absorptions E.AnswerEdge n (positions E) final) (normal : Normal E.AnswerEdge final) :
    final = [E.root] := by
  have single := normalized_iff_root E hr steps normal
  have nodup := steps.sublist.nodup (Section03.nodup_lookup M E.InS)
  cases final with
  | nil => exact False.elim (List.not_mem_nil ((single _).2 rfl))
  | cons x xs =>
    have eq := (single x).1 List.mem_cons_self
    subst x
    cases xs with
    | nil => rfl
    | cons y ys =>
      have hy := (single y).1 (List.mem_cons_of_mem _ List.mem_cons_self)
      exact False.elim ((List.nodup_cons.mp nodup).1 (hy ▸ List.mem_cons_self))

end Selected

#print axioms Absorptions.cover
#print axioms exists_normalization
#print axioms normal_iff_top
#print axioms singleton_iff_reaches_all
#print axioms absorption_preserves_answer
#print axioms retained_occurrence
#print axioms normalized_eq_singleton

end SemanticChains.Section04
