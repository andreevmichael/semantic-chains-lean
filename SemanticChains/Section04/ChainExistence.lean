import SemanticChains.Section04.SingleLink
import SemanticChains.Section04.Normalization

/-! §4.2. Однозвенная цепочка для условий MainTheorem. В обеих граничных
позициях используется один объект o фиксированного контракта. -/

namespace SemanticChains.Section04

open LemmaOne (State InQuestion InFullAnswer)

variable {T : State} {Fact I : Type} {M : ChainModel T Fact I} {E : Expansion M}

/-- Каждое вхождение указывает на запись в полном представлении родителя
(ContractGraph.parentFull и atAddress). По пути используются именно эти вхождения. -/
private def occurrencePath {p f : Fact} : Path E.AnswerEdge p f → Path M.presentation.Occurrence p f
  | .here x => .here x
  | .step edge tail => .step (E.toContractEdge edge).val (occurrencePath tail)

private theorem singleton_split {α : Type} {x y : α} {pre post : List α}
    (h : [x] = pre ++ y :: post) : pre = [] ∧ y = x ∧ post = [] := by
  simpa [List.singleton_eq_append_iff, and_assoc] using h

/-- П1–П5 и С1–С6 для полного начального текста одного звена. -/
private theorem full_singleton_supports {Q : String} {a : T.Content} {v : Reading T} {o : T.Obj}
    (full : M.presentation.Full E.root v) (enough : M.Entails (M.factContent E.root) a)
    (role : M.expresses Q a E.root) (inQ : InQuestion T Q o)
    (designates : M.presentation.Designates v o) (inA : InFullAnswer T a o) :
    M.Supports E Q a [(E.root, v)] [o, o] o := by
  apply ChainModel.Supports.full (by simpa using full)
  refine ⟨by simp, by simp, ?_, ?_, ?_, trivial, ?_, inQ, inA, ?_⟩
  · intro l hl
    obtain rfl := List.mem_singleton.mp hl
    exact E.root_mem
  · intro pre l post h
    obtain ⟨rfl, rfl, rfl⟩ := singleton_split h
    exact M.full_contributes role full
  · intro i holds
    have text := holds (E.root, v) List.mem_cons_self
    rw [M.full_content full] at text
    exact enough i text
  · exact ⟨inQ, designates, designates, inA, trivial⟩
  · exact ⟨_, List.mem_cons_self, designates⟩

/-- Сокращение разрешено, пока новое предъявление поддерживает тот же ответ
с тем же основанием и обоими прежними ключами. Минимум берётся только
среди текстов, достижимых такими шагами из данного полного текста. -/
private theorem admissible_singleton {Q : String} {a : T.Content} {o : T.Obj} {start : Reading T}
    (initial : M.Supports E Q a [(E.root, start)] [o, o] o) :
    ∃ best, M.Admissible E Q a [(E.root, best)] o := by
  let supported v := M.SupportsNow E Q a [(E.root, v)] [o, o] o
  let edit v u := M.Cut E.root v u ∧ supported u
  obtain ⟨best, reached, least⟩ := exists_least_measure (fun t : Reading T => t.wording.length) (P := Edits edit start) start .refl
  have valid : M.Supports E Q a [(E.root, best)] [o, o] o := by
    clear least
    induction reached with
    | refl => exact initial
    | snoc _ last ih => exact .shorten (pre := []) (post := []) ih last.1 last.2
  refine ⟨best, [o, o], valid, ?_⟩
  intro pre f v post u h cut next
  obtain ⟨rfl, eq, rfl⟩ := singleton_split h
  cases eq
  exact (Nat.not_lt_of_ge (least u (.snoc reached ⟨cut, next⟩))) cut.2.2

/-- Построение в найденном графе. Предпосылки относятся к исходному
разбору и обозначению объекта. Обнаружение r, охват S, полная нормализация
и допустимость текста звена выводятся для одних и тех же r и o. -/
theorem found_singleton_chain {Q : String} {a : T.Content} {f : Fact} {o : T.Obj}
    (root : M.PossibleRoot Q a E.root) (selected : E.InS f)
    (recorded : M.graph.RecordedObject f o) (inQ : InQuestion T Q o) (inA : InFullAnswer T a o) :
    (∃ k, E.root ∈ Section03.ascent M Q k) ∧
    (∀ y, E.InS y → Section03.InW M (Section03.initialFacts M Q) y) ∧
    (∃ n, Absorptions E.AnswerEdge n (positions E) [E.root] ∧ Normal E.AnswerEdge [E.root]) ∧
    ∃ best, M.Admissible E Q a [(E.root, best)] o := by
  refine ⟨Section03.ascent_finds_root M selected inQ recorded,
    Section03.selected_subset_question_growth M selected inQ recorded, ?_⟩
  obtain ⟨n, final, steps, normal⟩ := exists_normalization E.AnswerEdge (positions E)
  obtain rfl := normalized_eq_singleton E root.registered steps normal
  refine ⟨⟨n, steps, normal⟩, ?_⟩
  have original : ∀ i, (∀ y ∈ positions E, M.holds (M.factContent y) i) → M.holds a i :=
    fun i holds => root.justifies i (holds E.root ((mem_positions E root.registered _).2 E.root_mem))
  have enough : M.Entails (M.factContent E.root) a := by
    intro i holds
    apply absorption_preserves_answer E steps original i
    intro y hy
    simpa only [List.mem_singleton.mp hy] using holds
  obtain ⟨x, hx, ⟨address⟩⟩ := steps.cover ((mem_positions E root.registered f).2 selected)
  obtain rfl := List.mem_singleton.mp hx
  obtain ⟨v, full, key⟩ := M.full_for_recorded_object recorded
  obtain ⟨start, fullRoot, rootKey⟩ := present_at_root M.presentation (occurrencePath address) full key
  exact admissible_singleton (full_singleton_supports fullRoot enough root.expresses inQ rootKey inA)

/-- Основная теорема статьи в исходной формулировке. Принадлежность
объекта вопросу и полному ответу берётся для конкретного носителя по К7. -/
theorem main_theorem (M : ChainModel T Fact I) : MainTheorem M := by
  intro Q A a E _anchored _full root carrier
  obtain ⟨f, o, selected, recorded, inQ, inA⟩ := carrier
  obtain ⟨_, _, _, best, valid⟩ := found_singleton_chain root selected recorded inQ inA
  exact ⟨[(E.root, best)], o, valid⟩

#print axioms found_singleton_chain
#print axioms main_theorem

end SemanticChains.Section04
