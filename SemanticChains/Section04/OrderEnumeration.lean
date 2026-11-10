import SemanticChains.Section04.LinkExpansion

/-! §4.4. Совместная проверка текстов и перебор порядков оснований. -/
namespace SemanticChains.Section04

variable {T : LemmaOne.State} {Fact I : Type} {M : ChainModel T Fact I} {E : Expansion M}

def totalTextLength {T : LemmaOne.State} {Fact : Type} (links : List (Link T Fact)) : Nat :=
  (links.map (fun l => l.2.wording.length)).sum

/-- Один шаг меняет текст одного звена. Весь новый набор проверяется
с прежними основаниями, ключами переходов и общим объектом. -/
inductive TupleCut (E : Expansion M) (Q : String) (a : T.Content) (keys : List T.Obj) (o : T.Obj) :
    List (Link T Fact) → List (Link T Fact) → Prop where
  | replace {pre post f v u} : M.Cut f v u →
      M.SupportsNow E Q a (pre ++ (f, u) :: post) keys o →
      TupleCut E Q a keys o (pre ++ (f, v) :: post) (pre ++ (f, u) :: post)

/-- Если вопрос, все тексты и полный ответ обозначают o, на каждой
границе можно использовать o. Структурное соседство и обоснование ответа
по-прежнему проверяются условиями Supports. -/
theorem common_key_transitions {Q : String} {a : T.Content} {o : T.Obj} (links : List (Link T Fact))
    (inQ : LemmaOne.InQuestion T Q o) (inA : LemmaOne.InFullAnswer T a o)
    (allTexts : ∀ l ∈ links, M.presentation.Designates l.2 o) :
    ChainModel.keyed (boundaries M Q a links) (List.replicate (links.length + 1) o) := by
  have walk (left : T.Obj → Prop) (xs : List (Link T Fact)) (first : left o)
      (each : ∀ l ∈ xs, M.presentation.Designates l.2 o) :
      ChainModel.keyed (T := T) (left :: xs.map (fun l => M.presentation.Designates l.2) ++
        [LemmaOne.InFullAnswer T a]) (List.replicate (xs.length + 1) o) := by
    induction xs generalizing left with
    | nil => exact ⟨first, inA, trivial⟩
    | cons l tail ih =>
      have next := each l List.mem_cons_self
      exact ⟨first, next, ih _ next (fun t ht => each t (List.mem_cons_of_mem _ ht))⟩
  exact walk _ links inQ allTexts

/-- Среди достижимых из данного набора есть набор наименьшей суммарной
длины. Каждый его текст минимален при фиксированных остальных текстах. -/
theorem minimize_tuple {Q : String} {a : T.Content} {start : List (Link T Fact)}
    {keys : List T.Obj} {o : T.Obj} (valid : M.Supports E Q a start keys o) :
    let edit := TupleCut E Q a keys o
    ∃ best, Edits edit start best ∧ best.map Prod.fst = start.map Prod.fst ∧
      (∀ other, Edits edit start other → totalTextLength best ≤ totalTextLength other) ∧
      M.Supports E Q a best keys o ∧ M.Admissible E Q a best o := by
  let edit := TupleCut E Q a keys o
  obtain ⟨best, reached, least⟩ := exists_least_measure totalTextLength (P := Edits edit start) start .refl
  have order : best.map Prod.fst = start.map Prod.fst := by
    clear least
    induction reached with
    | refl => rfl
    | snoc _ last ih =>
      cases last
      simpa only [List.map_append, List.map_cons] using ih
  have supported : M.Supports E Q a best keys o := by
    clear least order
    induction reached with
    | refl => exact valid
    | snoc _ last ih =>
      cases last with
      | replace cut accepted => exact .shorten ih cut accepted
  refine ⟨best, reached, order, least, supported, keys, supported, ?_⟩
  rintro pre f v post u rfl cut next
  have le := least _ (.snoc reached (.replace cut next))
  have short := cut.2.2
  simp only [totalTextLength, List.map_append, List.map_cons, List.sum_append_nat, List.sum_cons] at le
  omega

/-- Выбираем k оснований по порядку. Использованное основание удаляется
из пула до выбора следующего. При k = 0 имеется один пустой хвост. -/
def ordersOfLength {F : Type} [DecidableEq F] (pool : List F) : Nat → List (List F)
  | 0 => [[]]
  | k + 1 => pool.flatMap fun f => (ordersOfLength (pool.erase f) k).map (f :: ·)

theorem mem_ordersOfLength {F : Type} [DecidableEq F] {pool order : List F}
    (unique : pool.Nodup) (k : Nat) :
    order ∈ ordersOfLength pool k ↔ order.length = k ∧ order.Nodup ∧ order ⊆ pool := by
  induction k generalizing pool order with
  | zero => cases order <;> simp [ordersOfLength]
  | succ k ih =>
    cases order with
    | nil => simp [ordersOfLength]
    | cons x xs =>
      simp only [ordersOfLength, List.mem_flatMap, List.mem_map, List.cons.injEq]
      constructor
      · rintro ⟨_, hx, _, rest, rfl, rfl⟩
        obtain ⟨len, nd, sub⟩ := (ih (List.erase_sublist.nodup unique)).1 rest
        refine ⟨by simp [len], List.nodup_cons.mpr ⟨fun hit => unique.not_mem_erase (sub hit), nd⟩, ?_⟩
        exact List.cons_subset.mpr ⟨hx, fun _ hit => List.mem_of_mem_erase (sub hit)⟩
      · rintro ⟨len, nd, sub⟩
        obtain ⟨fresh, nd⟩ := List.nodup_cons.mp nd
        obtain ⟨hx, sub⟩ := List.cons_subset.mp sub
        refine ⟨x, hx, xs, (ih (List.erase_sublist.nodup unique)).2 ⟨by simpa using len, nd, ?_⟩, rfl, rfl⟩
        intro y hy
        exact unique.mem_erase_iff.mpr ⟨fun h => fresh (h ▸ hy), sub hy⟩

private theorem order_length_bound {F : Type} [DecidableEq F] {pool order : List F}
    (nd : order.Nodup) (sub : order ⊆ pool) : order.length ≤ pool.length := by
  induction order generalizing pool with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, nd⟩ := List.nodup_cons.mp nd
    obtain ⟨hx, sub⟩ := List.cons_subset.mp sub
    have bound := ih nd (show xs ⊆ pool.erase x from fun y hy =>
      (List.mem_erase_of_ne (show y ≠ x from fun h => fresh (h ▸ hy))).mpr (sub hy))
    rw [List.length_erase_of_mem hx] at bound
    have pos := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

/-- D перечисляется без повторов, даже при нескольких путях к одному факту. -/
noncomputable def underlyingPool (E : Expansion M) : List Fact :=
  Section03.lookup M fun f => E.InS f ∧ f ≠ E.root

private theorem mem_pool (E : Expansion M) (hr : E.root ∈ M.registered) (f : Fact) :
    f ∈ underlyingPool E ↔ E.InS f ∧ f ≠ E.root := by
  rw [underlyingPool, Section03.mem_lookup]
  exact ⟨And.right, fun h => ⟨E.subset_contract hr h.1, h⟩⟩

def enumerateOrders {F : Type} [DecidableEq F] (root : F) (pool : List F) :=
  [root] :: (List.range pool.length).flatMap (fun i => ordersOfLength pool (i + 1))

noncomputable def candidates (E : Expansion M) : List (List Fact) := by
  classical exact enumerateOrders E.root (underlyingPool E)

/-- Утверждение 4.4. Членство в перечислении равносильно принадлежности
заданному классу. Порядок следования фактов произволен, включая чередование ветвей. -/
theorem mem_candidates (E : Expansion M) (hr : E.root ∈ M.registered) (order : List Fact) :
    order ∈ candidates E ↔ order = [E.root] ∨
      order ≠ [] ∧ order.Nodup ∧ ∀ f ∈ order, E.InS f ∧ f ≠ E.root := by
  classical
  let pool := underlyingPool E
  have unique : pool.Nodup := Section03.nodup_lookup M _
  change order ∈ enumerateOrders E.root pool ↔ _
  simp only [enumerateOrders, List.mem_cons, List.mem_flatMap, List.mem_range]
  apply or_congr_right
  constructor
  · rintro ⟨i, _, hit⟩
    obtain ⟨len, nd, sub⟩ := (mem_ordersOfLength unique _).1 hit
    refine ⟨fun empty => ?_, nd, fun f hf => (mem_pool E hr f).1 (sub hf)⟩
    simp [empty] at len
  · rintro ⟨nonempty, nd, inside⟩
    have sub : order ⊆ pool := fun f h => (mem_pool E hr f).2 (inside f h)
    have bound := order_length_bound nd sub
    have pos := List.length_pos_iff.mpr nonempty
    refine ⟨order.length - 1, by omega, (mem_ordersOfLength unique _).2 ⟨by omega, nd, sub⟩⟩

/-- Число выборов без возвращения. При k ≤ n оно равно n!/(n-k)!. -/
def orderCount (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => n * orderCount (n - 1) k

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

private theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (Nat.succ_pos _) ih

theorem orderCount_factorial {n k : Nat} (bound : k ≤ n) :
    orderCount n k = factorial n / factorial (n - k) := by
  have product (n k : Nat) (h : k ≤ n) :
      factorial n = orderCount n k * factorial (n - k) := by
    induction k generalizing n with
    | zero => simp [orderCount]
    | succ k ih =>
      cases n with
      | zero => omega
      | succ n =>
        have prev := ih n (by omega)
        calc
          factorial (n + 1) = (n + 1) * factorial n := rfl
          _ = (n + 1) * (orderCount n k * factorial (n-k)) := congrArg _ prev
          _ = _ := by simp [orderCount, Nat.mul_assoc]
  exact (Nat.div_eq_of_eq_mul_left (factorial_pos _) (product n k bound)).symm

theorem length_ordersOfLength {F : Type} [DecidableEq F] (pool : List F) (k : Nat) :
    (ordersOfLength pool k).length = orderCount pool.length k := by
  induction k generalizing pool with
  | zero => rfl
  | succ k ih =>
    rw [ordersOfLength, List.length_flatMap]
    have counts := List.map_congr_left (l := pool) (g := fun _ => orderCount (pool.length - 1) k)
      (f := fun x => ((ordersOfLength (pool.erase x) k).map (x :: ·)).length)
      (fun x hx => by simp only [List.length_map, ih, List.length_erase_of_mem hx])
    rw [counts, List.map_const', List.sum_replicate_nat]
    rfl

theorem nodup_ordersOfLength {F : Type} [DecidableEq F] {pool : List F}
    (nd : pool.Nodup) (k : Nat) : (ordersOfLength pool k).Nodup := by
  induction k generalizing pool with
  | zero => simp [ordersOfLength]
  | succ k ih =>
    apply List.pairwise_flatMap.mpr
    constructor
    · intro x _
      apply List.pairwise_map.mpr
      exact (ih (pool := pool.erase x) (nd.erase x)).imp (fun h eq => h (List.cons.inj eq).2)
    · apply nd.imp
      intro x y distinct u hu v hv
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hu
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      exact fun eq => distinct (List.cons.inj eq).1

/-- Число всех кандидатов с учётом отдельного варианта [r]. -/
theorem candidate_count (E : Expansion M) :
    let n := (underlyingPool E).length
    (candidates E).length = 1 + ((List.range n).map
      (fun i => factorial n / factorial (n - (i+1)))).sum := by
  classical
  let pool := underlyingPool E
  change (enumerateOrders E.root pool).length = _
  rw [enumerateOrders, List.length_cons, List.length_flatMap, Nat.add_comm]
  congr 2
  apply List.map_congr_left
  intro i hi
  exact (length_ordersOfLength pool (i+1)).trans (orderCount_factorial (List.mem_range.mp hi))

theorem candidates_nodup (E : Expansion M) : (candidates E).Nodup := by
  classical
  let pool := underlyingPool E
  have unique : pool.Nodup := Section03.nodup_lookup M _
  change ([E.root] :: (List.range pool.length).flatMap (fun i => ordersOfLength pool (i+1))).Nodup
  apply List.nodup_cons.mpr
  constructor
  · intro h
    obtain ⟨i, _, hit⟩ := List.mem_flatMap.mp h
    have member := ((mem_ordersOfLength unique _).1 hit).2.2 List.mem_cons_self
    exact ((Section03.mem_lookup M _ _).1 member).2.2 rfl
  · apply List.pairwise_flatMap.mpr
    refine ⟨fun _ _ => nodup_ordersOfLength unique _, List.nodup_range.imp ?_⟩
    intro i j ne x hx y hy eq
    subst y
    have first := ((mem_ordersOfLength unique _).1 hx).1
    have second := ((mem_ordersOfLength unique _).1 hy).1
    omega

/-- Кандидат проходит проверку тогда и только тогда, когда существует
допустимая цепочка с теми же основаниями и в том же порядке. -/
theorem compatible_iff_admissible (E : Expansion M) (Q : String) (a : T.Content)
    (order : List Fact) (o : T.Obj) :
    (∃ links keys, links.map Prod.fst = order ∧ M.Supports E Q a links keys o) ↔
    (∃ links, links.map Prod.fst = order ∧ M.Admissible E Q a links o) := by
  constructor
  · rintro ⟨links, keys, eq, valid⟩
    obtain ⟨best, _, same, _, _, admissible⟩ := minimize_tuple valid
    exact ⟨best, same.trans eq, admissible⟩
  · rintro ⟨links, eq, keys, valid, _⟩
    exact ⟨links, keys, eq, valid⟩

/-- Полнота отбора внутри класса статьи: [r] либо порядок без r.
Существование совместимых текстов проверяется отдельно от перечисления. -/
theorem accepted_orders_iff (E : Expansion M) (hr : E.root ∈ M.registered)
    (Q : String) (a : T.Content) (order : List Fact) (o : T.Obj) :
    (order ∈ candidates E ∧ ∃ links keys, links.map Prod.fst = order ∧ M.Supports E Q a links keys o) ↔
    ((order = [E.root] ∨ E.root ∉ order) ∧
      ∃ links, links.map Prod.fst = order ∧ M.Admissible E Q a links o) := by
  rw [mem_candidates E hr, compatible_iff_admissible]
  constructor
  · rintro ⟨member, witness⟩
    refine ⟨?_, witness⟩
    rcases member with root | ⟨_, _, nested⟩
    · exact Or.inl root
    · exact Or.inr (fun h => (nested _ h).2 rfl)
  · rintro ⟨scope, links, rfl, admissible⟩
    refine ⟨?_, links, rfl, admissible⟩
    rcases scope with root | noRoot
    · exact Or.inl root
    · obtain ⟨keys, supported, _⟩ := admissible
      obtain ⟨nonempty, unique, node, _⟩ := supported.now
      refine Or.inr ⟨by simpa using nonempty, unique, ?_⟩
      intro f hf
      obtain ⟨l, hl, eq⟩ := List.mem_map.mp hf
      exact ⟨eq ▸ node l hl, fun same => noRoot (same ▸ hf)⟩

/-- Кандидат [r] проходит отбор при тех же условиях, что и в §4.2. -/
theorem root_order_accepted {Q : String} {a : T.Content} {f : Fact} {o : T.Obj}
    (root : M.PossibleRoot Q a E.root) (selected : E.InS f)
    (recorded : M.graph.RecordedObject f o) (inQ : LemmaOne.InQuestion T Q o)
    (inA : LemmaOne.InFullAnswer T a o) :
    [E.root] ∈ candidates E ∧ ∃ links keys, links.map Prod.fst = [E.root] ∧
      M.Supports E Q a links keys o := by
  obtain ⟨_, _, _, best, verified⟩ := found_singleton_chain root selected recorded inQ inA
  exact (accepted_orders_iff E root.registered Q a [E.root] o).2
    ⟨Or.inl rfl, [(E.root, best)], rfl, verified⟩

#print axioms root_order_accepted
#print axioms common_key_transitions
#print axioms minimize_tuple
#print axioms mem_candidates
#print axioms candidates_nodup
#print axioms candidate_count
#print axioms accepted_orders_iff

end SemanticChains.Section04
