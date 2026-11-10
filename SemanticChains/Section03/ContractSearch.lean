import SemanticChains.Section02.QuestionInGraph

/-! §3.1. Запросы к логическим фактам одного фиксированного контракта.
Реестр конечен, но проверка интерпретаций здесь задана математически.
Для выполнения перебора нужны процедуры распознавания его предикатов. -/

namespace SemanticChains.Section03

open LemmaOne (State)

variable {T : State} {Fact I : Type} (M : ChainModel T Fact I)

inductive Query (Obj Fact : Type) where
  | object (o : Obj)
  | parents (child : Fact)
  | children (parent : Fact)

def Matches : Query T.Obj Fact → Fact → Prop
  | .object o, f => M.graph.RecordedObject f o
  | .parents c, p => Nonempty (M.graph.Edge p c)
  | .children p, c => Nonempty (M.graph.Edge p c)

/-- Один проход по конечному реестру. В результирующем списке каждый
логический факт встречается один раз, даже если повторяется в реестре. -/
private def collect {F : Type} [DecidableEq F] (accept : F → Prop) [DecidablePred accept] :
    List F → List F
  | [] => []
  | f :: fs => if accept f then (collect accept fs).insert f else collect accept fs

private theorem mem_collect {F : Type} [DecidableEq F] (accept : F → Prop)
    [DecidablePred accept] (fs : List F) (x : F) :
    x ∈ collect accept fs ↔ x ∈ fs ∧ accept x := by
  induction fs with
  | nil => simp [collect]
  | cons f fs ih =>
    by_cases h : accept f
    · simp only [collect, if_pos h, List.mem_insert_iff, List.mem_cons, ih]
      grind
    · simp only [collect, if_neg h, List.mem_cons, ih]
      grind

private theorem nodup_collect {F : Type} [DecidableEq F] (accept : F → Prop)
    [DecidablePred accept] (fs : List F) : (collect accept fs).Nodup := by
  induction fs with
  | nil => simp [collect]
  | cons f fs ih =>
    by_cases ok : accept f
    · simp only [collect, if_pos ok]
      by_cases present : f ∈ collect accept fs
      · simpa only [List.insert_of_mem present] using ih
      · rw [List.insert_of_not_mem present, List.nodup_cons]
        exact ⟨present, ih⟩
    · simpa only [collect, if_neg ok] using ih

/-- Результат запроса является подпоследовательностью реестра, в том числе
при повторных записях одного факта (Т12). -/
private theorem collect_sublist {F : Type} [DecidableEq F] (accept : F → Prop)
    [DecidablePred accept] (fs : List F) : (collect accept fs).Sublist fs := by
  induction fs with
  | nil => exact .slnil
  | cons f fs ih =>
    by_cases ok : accept f
    · simp only [collect, if_pos ok]
      by_cases present : f ∈ collect accept fs
      · rw [List.insert_of_mem present]
        exact .cons f ih
      · rw [List.insert_of_not_mem present]
        exact .cons₂ f ih
    · simpa only [collect, if_neg ok] using ih.cons f

noncomputable def lookup (accept : Fact → Prop) : List Fact := by
  classical exact collect accept M.registered

theorem mem_lookup (accept : Fact → Prop) (f : Fact) :
    f ∈ lookup M accept ↔ f ∈ M.registered ∧ accept f := by
  classical exact mem_collect _ _ _

theorem nodup_lookup (accept : Fact → Prop) : (lookup M accept).Nodup := by
  classical exact nodup_collect _ _

theorem length_lookup_le (accept : Fact → Prop) :
    (lookup M accept).length ≤ M.registered.length := by
  classical exact (collect_sublist accept M.registered).length_le

noncomputable def run (q : Query T.Obj Fact) : List Fact := lookup M (Matches M q)

/-- Точность и полнота каждого из трёх запросов относительно всего K. -/
theorem mem_run (q : Query T.Obj Fact) (f : Fact) :
    f ∈ run M q ↔ f ∈ M.registered ∧ Matches M q f := by
  exact mem_lookup M _ f

theorem nodup_run (q : Query T.Obj Fact) : (run M q).Nodup := by
  exact nodup_lookup M _

/-- Оба направления поиска возвращают одно и то же засвидетельствованное ребро. -/
theorem parents_iff_children (p c : Fact) :
    p ∈ run M (.parents c) ↔ c ∈ run M (.children p) := by
  rw [mem_run, mem_run]
  constructor
  · rintro ⟨_, ⟨edge⟩⟩
    exact ⟨edge.property.2.1, ⟨edge⟩⟩
  · rintro ⟨_, ⟨edge⟩⟩
    exact ⟨edge.property.1, ⟨edge⟩⟩

/-- Запрос участий факта по интерпретированному обозначению, с учётом
адреса. Запись может прямо назвать факт или отсылать к нему. -/
noncomputable def parentsByReading (address : T.Occ) (text : String) : List Fact :=
  lookup M fun p => ∃ f, M.graph.Represents f address text ∧ Nonempty (M.graph.Edge p f)

/-- Каждый результат запроса по записи имеет два свидетельства:
чтение записи как факта и ребро от найденного родителя к этому факту. -/
theorem mem_parents_by_reading (address : T.Occ) (text : String) (p : Fact) :
    p ∈ parentsByReading M address text ↔
      ∃ f, M.graph.Represents f address text ∧ Nonempty (M.graph.Edge p f) := by
  unfold parentsByReading
  rw [mem_lookup]
  refine ⟨And.right, ?_⟩
  rintro ⟨f, reading, ⟨edge⟩⟩
  exact ⟨edge.property.1, f, reading, ⟨edge⟩⟩

/-- Любое подтверждённое обозначение f даёт тот же список родителей, что и
запрос по f. Поэтому замена обозначения синонимичным сохраняет все результаты. -/
theorem parents_by_reading {address : T.Occ} {text : String} {f : Fact}
    (verified : M.graph.Represents f address text) :
    parentsByReading M address text = run M (.parents f) := by
  unfold parentsByReading run
  apply congrArg (lookup M)
  funext p
  apply propext
  constructor
  · rintro ⟨g, read, edge⟩
    have eq : g = f := Section02.same_vertex read verified rfl
    exact eq ▸ edge
  · exact fun edge => ⟨f, verified, edge⟩

theorem object_match_found {Q : String} {e : T.Occ} {f : Fact}
    (hit : Section02.ObjectMatch M Q e f) : f ∈ run M (.object hit.object) :=
  (mem_run M _ _).2 ⟨hit.represented.1, hit.address, hit.wording, hit.represented, hit.designated⟩

/-- В конечном реестре все факты, которые когда-либо будут открыты
возрастающим поиском, уже представлены на одном конечном шаге. -/
theorem finite_search_stage (stages : Nat → List Fact)
    (registered : ∀ {n p}, p ∈ stages n → p ∈ M.registered)
    (mono : ∀ {n m p}, n ≤ m → p ∈ stages n → p ∈ stages m) :
    ∃ N, ∀ p, (∃ n, p ∈ stages n) ↔ p ∈ stages N := by
  classical
  have bound (fs : List Fact) : ∃ N, ∀ p ∈ fs,
      (∃ n, p ∈ stages n) → p ∈ stages N := by
    induction fs with
    | nil => exact ⟨0, by simp⟩
    | cons f fs ih =>
      obtain ⟨N, covered⟩ := ih
      by_cases found : ∃ k, f ∈ stages k
      · obtain ⟨k, hit⟩ := found
        refine ⟨max N k, ?_⟩
        intro p hp ever
        rcases List.mem_cons.mp hp with rfl | rest
        · exact mono (Nat.le_max_right _ _) hit
        · exact mono (Nat.le_max_left _ _) (covered p rest ever)
      · refine ⟨N, ?_⟩
        intro p hp ever
        rcases List.mem_cons.mp hp with rfl | rest
        · exact False.elim (found ever)
        · exact covered p rest ever
  obtain ⟨N, covered⟩ := bound M.registered
  exact ⟨N, fun p => ⟨fun ⟨n, hit⟩ => covered p (registered hit) ⟨n, hit⟩,
    fun hit => ⟨N, hit⟩⟩⟩

#print axioms mem_run
#print axioms parents_by_reading
#print axioms parents_iff_children

end SemanticChains.Section03
