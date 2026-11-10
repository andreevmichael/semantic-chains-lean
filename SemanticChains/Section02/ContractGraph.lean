import SemanticChains.MainTheorem

/-! §2.1. Следствия определения G_K и связь с выбранным раскрытием. -/
namespace SemanticChains.Section02

open LemmaOne (State)

variable {T : State} {Fact I : Type} {M : ChainModel T Fact I}

/-- Конечный реестр перечисляет все вершины. Повтор в перечислении
не создаёт нового логического факта. -/
theorem vertex_iff_index (f : Fact) :
    f ∈ M.registered ↔ ∃ i : Fin M.registered.length, M.registered.get i = f :=
  List.mem_iff_get

/-- Две интерпретации с одним полным содержанием дают одну вершину,
даже если адреса и строки различны (Т8.4). -/
theorem same_vertex {f g : Fact} {addr addr' : T.Occ} {v v' : String}
    (first : M.graph.Represents f addr v) (second : M.graph.Represents g addr' v')
    (same : T.interpret addr v = T.interpret addr' v') : f = g := by
  apply M.graph.identity_of_content first.1 second.1
  exact Option.some.inj (first.2.symm.trans (same.trans second.2))

/-- Полный текст зарегистрированного факта входит в его семейство. -/
theorem full_in_family {f : Fact} {v : Reading T} (registered : f ∈ M.registered)
    (full : M.presentation.Full f v) : M.graph.Family f v.wording :=
  ⟨v.address, registered, (M.full_content full) ▸ v.verified⟩

/-- Простая отсылка или посылка вывода сама по себе не даёт сохраняющего ребра. -/
theorem no_edge_without_preservation {p c : Fact} (h : ¬ M.graph.preserves p c) :
    ¬ Nonempty (M.graph.Edge p c) := fun ⟨w⟩ => h (M.graph.keeps w.val)

/-- Каждая выбранная стрелка входит в E_K. Обратное утверждение
требовало бы выбора данного вхождения. -/
def contractPath {E : Expansion M} {p f : Fact} :
    Path E.Edge p f → Path M.graph.Edge p f
  | .here x => .here x
  | .step edge tail => .step edge.val (contractPath tail)

/-- Полное сохранение вдоль пути следует из свидетельств отдельных рёбер. -/
theorem path_preserves {p f : Fact} (path : Path M.graph.Edge p f) :
    M.graph.preserves p f := by
  induction path with
  | here x => exact M.graph.refl x
  | step e _ ih => exact M.graph.trans (M.graph.keeps e.val) ih

theorem path_entails {p f : Fact} (path : Path M.graph.Edge p f) :
    M.Entails (M.factContent p) (M.factContent f) := M.preservation_sound (path_preserves path)

/-- После строгого ребра вернуться к его началу по сохраняющим стрелкам
невозможно: взаимное сохранение отождествило бы его различные концы. -/
theorem no_return {p c : Fact} (edge : M.graph.Edge p c) :
    ¬ Nonempty (Path M.graph.Edge c p) := by
  rintro ⟨back⟩
  have eqContent := M.graph.mutual_content (M.graph.keeps edge.val) (path_preserves back)
  exact edge.property.2.2 (M.graph.identity_of_content edge.property.1 edge.property.2.1 eqContent)

/-- К верхнему основанию контрактного графа ведёт только путь длины ноль.
В частности, наличие общего подфакта у двух различных верхних оснований
не даёт пути от одного из них к другому. -/
theorem path_to_top {p f : Fact} (path : Path M.graph.Edge p f) :
    M.graph.IsTop f → p = f := by
  induction path with
  | here => exact fun _ => rfl
  | step edge tail ih =>
    intro top
    cases ih top
    exact False.elim (top.2 _ ⟨edge⟩)

/-- Конструкция x ← p → y. Для прямого поворота нужны участники одного
отношения p и их роли в конкретных выбранных вхождениях. -/
theorem connected_via_parent {E : Expansion M} {p x y : Fact}
    (parent : E.InS p) (left : E.Edge p x) (right : E.Edge p y) (distinct : x ≠ y)
    (relation : M.graph.CommonRelation left.val.val right.val.val) :
    E.Connected x y := by
  refine ⟨p, parent, .step left (.here x), .step right (.here y), ?_, relation⟩
  have hpx : p ≠ x := left.val.property.2.2
  have hpy : p ≠ y := right.val.property.2.2
  simp [Path.vertices, List.nodup_cons, Ne.symm hpx, hpy, distinct]

#print axioms same_vertex
#print axioms no_return
#print axioms connected_via_parent

end SemanticChains.Section02
