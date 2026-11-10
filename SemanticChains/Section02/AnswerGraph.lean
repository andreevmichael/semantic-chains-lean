import SemanticChains.Section02.ContractGraph

/-! §2.3. Граф ответа и пределы раскрытия. S строится по выбранным
вхождениям от r в одном состоянии контракта, до введения поисковой области W. -/
namespace SemanticChains

def Path.append {F : Type} {R : F → F → Type} {a b c : F}
    (first : Path R a b) (rest : Path R b c) : Path R a c :=
  match first with
  | .here _ => rest
  | .step w tail => .step w (tail.append rest)

namespace Expansion

variable {T : LemmaOne.State} {F I : Type} {M : ChainModel T F I} (E : Expansion M)

theorem root_mem : E.InS E.root := ⟨.here E.root⟩

theorem mem_of_step {p f : F} (hp : E.InS p) (w : E.Edge p f) : E.InS f := by
  obtain ⟨path⟩ := hp
  exact ⟨path.append (.step w (.here f))⟩

/-- Стрелка Γ_S хранит именно выбранное вхождение из уже достигнутого
родителя. Выбор в другом компоненте контракта не меняет Γ_S. -/
def AnswerEdge (p f : F) := {_w : E.Edge p f // E.InS p}

/-- Забываем только ограничение на выбор. Свидетельство вхождения вместе
с адресом и ролью остаётся тем же, в том числе для выведенных фактов. -/
def toContractEdge {p f : F} (w : E.AnswerEdge p f) : M.graph.Edge p f := w.val.val

theorem edge_endpoints {p f : F} (w : E.AnswerEdge p f) : E.InS p ∧ E.InS f :=
  ⟨w.property, E.mem_of_step w.property w.val⟩

private def restrictPath {p f : F} (path : Path E.Edge p f) (hp : E.InS p) :
    Path E.AnswerEdge p f :=
  match path with
  | .here x => .here x
  | .step w tail => .step ⟨w, hp⟩ (restrictPath tail (E.mem_of_step hp w))

private def selectedPath {p f : F} : Path E.AnswerEdge p f → Path E.Edge p f
  | .here x => .here x
  | .step w tail => .step w.val (selectedPath tail)

/-- D_S(r) = S: путь можно пройти целиком внутри Γ_S. -/
theorem reachable_iff_mem {f : F} : Nonempty (Path E.AnswerEdge E.root f) ↔ E.InS f := by
  constructor
  · rintro ⟨path⟩
    exact ⟨E.selectedPath path⟩
  · rintro ⟨path⟩
    exact ⟨E.restrictPath path E.root_mem⟩

private theorem endpoint_registered {p f : F} (path : Path E.Edge p f) :
    p ∈ M.registered → f ∈ M.registered := by
  induction path with
  | here => exact id
  | step w _ ih => exact fun _ => ih w.val.property.2.1

theorem subset_contract (hr : E.root ∈ M.registered) {f : F} (hf : E.InS f) :
    f ∈ M.registered := by
  obtain ⟨path⟩ := hf
  exact E.endpoint_registered path hr

/-- Даже при повторных вхождениях подфакта число различных вершин S
ограничено длиной конечного реестра. Выбор индекса не задаёт алгоритм поиска. -/
theorem finite_vertices (hr : E.root ∈ M.registered) :
    ∃ index : {f // E.InS f} → Fin M.registered.length,
      ∀ f, M.registered.get (index f) = f.val := by
  have indexed (f : {f // E.InS f}) := (Section02.vertex_iff_index f.val).mp
    (E.subset_contract hr f.property)
  exact ⟨fun f => Classical.choose (indexed f), fun f => Classical.choose_spec (indexed f)⟩

def IsTop (f : F) : Prop := E.InS f ∧ ∀ p, ¬ Nonempty (E.AnswerEdge p f)

private theorem last_edge_or_start {p f : F} (path : Path E.AnswerEdge p f) :
    f = p ∨ ∃ parent, Nonempty (E.AnswerEdge parent f) := by
  induction path with
  | here => exact Or.inl rfl
  | step w _ ih =>
    rcases ih with rfl | incoming
    · exact Or.inr ⟨_, ⟨w⟩⟩
    · exact Or.inr incoming

/-- Утверждение 2.3 о верхней вершине. В r не входит строгое ребро из S,
а любой отличный от r элемент S имеет последнее ребро пути из r. -/
theorem top_iff_root {f : F} : E.IsTop f ↔ f = E.root := by
  constructor
  · rintro ⟨hf, top⟩
    obtain ⟨path⟩ := (E.reachable_iff_mem).mpr hf
    rcases E.last_edge_or_start path with eq | ⟨p, incoming⟩
    · exact eq
    · exact False.elim (top p incoming)
  · rintro rfl
    refine ⟨E.root_mem, ?_⟩
    rintro p ⟨w⟩
    obtain ⟨toParent⟩ := w.property
    exact Section02.no_return w.val.val ⟨Section02.contractPath toParent⟩

end Expansion

namespace Section02

variable {T : LemmaOne.State} {F I : Type} (M : ChainModel T F I)

/-- D_K(r) по всем сохраняющим рёбрам текущего контракта. -/
def Descendants (r f : F) : Prop :=
  f ∈ M.registered ∧ Nonempty (Path M.graph.Edge r f)

theorem descendants_nested {r y f : F} (toY : Path M.graph.Edge r y)
    (fromY : Descendants M y f) : Descendants M r f := by
  obtain ⟨hf, ⟨path⟩⟩ := fromY
  exact ⟨hf, ⟨toY.append path⟩⟩

theorem selected_subset_descendants (E : Expansion M) (hr : E.root ∈ M.registered)
    {f : F} (hf : E.InS f) : Descendants M E.root f := by
  refine ⟨E.subset_contract hr hf, ?_⟩
  obtain ⟨path⟩ := hf
  exact ⟨contractPath path⟩

/-- Если каждый зарегистрированный факт покрыт раскрытием одного из
оснований, достижимых из r, полное раскрытие r совпадает с K. -/
theorem covers_contract {r : F}
    (cover : ∀ f ∈ M.registered, ∃ y, Nonempty (Path M.graph.Edge r y) ∧ Descendants M y f) :
    ∀ f, Descendants M r f ↔ f ∈ M.registered := by
  intro f
  refine ⟨fun h => h.1, ?_⟩
  intro hf
  obtain ⟨y, ⟨path⟩, hy⟩ := cover f hf
  exact descendants_nested M path hy

#print axioms Expansion.finite_vertices
#print axioms Expansion.reachable_iff_mem
#print axioms Expansion.top_iff_root
#print axioms selected_subset_descendants
#print axioms covers_contract

end Section02
end SemanticChains
