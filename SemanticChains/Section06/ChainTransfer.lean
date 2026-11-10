import SemanticChains.Section04.OrderEnumeration

/-! §6.2. Перенос уже предъявленной цепочки в одном состоянии T:
вопрос, содержание ответа, выбранный граф и порядок оснований фиксированы. -/
namespace SemanticChains.Section06

open LemmaOne (State InQuestion InFullAnswer)

variable {T : State} {F I : Type} {M : ChainModel T F I} {E : Expansion M}

/-- В цепочке основания различны, поэтому новый текст можно задать по основанию. -/
def replaceText {T : State} (text : F → Reading T) (l : Link T F) : Link T F := (l.1, text l.1)

def SamePresentedContent (_M : ChainModel T F I) (text : F → Reading T) (links : List (Link T F)) : Prop :=
  ∀ l ∈ links, (replaceText text l).2.textContent = l.2.textContent

/-- Сравнивается фактически предъявленное содержание, в том числе у ранее
сокращённого текста. Совместное обоснование переносится в любом истолковании. -/
theorem transfer_justification {text : F → Reading T} {links : List (Link T F)} {a : T.Content}
    (same : SamePresentedContent M text links)
    (enough : ∀ i, (∀ l ∈ links, M.holds (l.2.textContent) i) → M.holds a i) :
    ∀ i, (∀ l ∈ links.map (replaceText text), M.holds (l.2.textContent) i) → M.holds a i := by
  intro i holds
  apply enough i
  intro l hl
  exact same l hl ▸ holds _ (List.mem_map.mpr ⟨l, hl, rfl⟩)

/-- На позиции проверяются только входящий и исходящий ключи этой позиции.
Обе проверки используют одну и ту же новую строку. -/
def RetainsKeys (M : ChainModel T F I) (text : F → Reading T) :
    List (Link T F) → List T.Obj → Prop
  | [], [_] => True
  | l :: rest, incoming :: outgoing :: tail =>
    (M.presentation.Designates l.2 incoming → M.presentation.Designates (text l.1) incoming) ∧
    (M.presentation.Designates l.2 outgoing → M.presentation.Designates (text l.1) outgoing) ∧
    RetainsKeys M text rest (outgoing :: tail)
  | _, _ => False

theorem transfer_keys {Q : String} {a : T.Content} {text : F → Reading T}
    {links : List (Link T F)} {keys : List T.Obj} (keep : RetainsKeys M text links keys)
    (old : ChainModel.keyed (Section04.boundaries M Q a links) keys) :
    ChainModel.keyed (Section04.boundaries M Q a (links.map (replaceText text))) keys := by
  let des (l : Link T F) := M.presentation.Designates l.2
  have walk (xs : List (Link T F)) (ks : List T.Obj) (incoming : T.Obj) (left newLeft : T.Obj → Prop)
      (boundary : left incoming → newLeft incoming) (hk : RetainsKeys M text xs (incoming :: ks))
      (previous : ChainModel.keyed (left :: xs.map des ++ [InFullAnswer T a]) (incoming :: ks)) :
      ChainModel.keyed (newLeft :: (xs.map (replaceText text)).map des ++ [InFullAnswer T a]) (incoming :: ks) := by
    induction xs generalizing ks incoming left newLeft with
    | nil =>
      cases ks with
      | nil => exact ⟨boundary previous.1, previous.2⟩
      | cons => exact False.elim hk
    | cons l xs ih =>
      cases ks with
      | nil => exact False.elim hk
      | cons outgoing tail =>
        exact ⟨boundary previous.1, hk.1 previous.2.1,
          ih tail outgoing _ _ hk.2.1 hk.2.2 previous.2.2⟩
  cases keys with
  | nil => cases links <;> exact False.elim keep
  | cons incoming ks => exact walk links ks incoming _ _ id keep old

/-- П5 в фиксированных Q и Â: оценка вклада по основанию и предъявленному
содержанию каждого звена с учётом его места в двух сравниваемых цепочках. Предикат
ChainModel.contributes получает строки, поэтому это свойство указывается явно. -/
def ContributionByContent (M : ChainModel T F I) (Q : String) (a : T.Content)
    (old new : List (Link T F)) : Prop :=
  ∃ rule : List (F × T.Content) → (F × T.Content) → List (F × T.Content) → Prop,
    ∀ pre l post, (old = pre ++ l :: post ∨ new = pre ++ l :: post) →
    let meaning := fun z : Link T F => (z.1, z.2.textContent)
    M.contributes Q a pre l post ↔ rule (pre.map meaning) (meaning l) (post.map meaning)

/-- Утверждение 6.2 для полной проверки Supports. Адресные свидетельства
обозначений интерпретируются в том же T. Общий объект достаточно сохранить
в одном из новых текстов; его позиция не фиксируется. -/
theorem transfer_supports_now {Q : String} {a : T.Content} {links : List (Link T F)}
    {keys : List T.Obj} {o : T.Obj} {text : F → Reading T} (old : M.Supports E Q a links keys o)
    (same : SamePresentedContent M text links)
    (p5 : ContributionByContent M Q a links (links.map (replaceText text)))
    (keep : RetainsKeys M text links keys)
    (common : ∃ l ∈ links, M.presentation.Designates (text l.1) o) :
    M.SupportsNow E Q a (links.map (replaceText text)) keys o := by
  obtain ⟨nonempty, distinct, represented, contributes, enough, neighbors, keyed, inQ, inA, _⟩ := old.now
  have order : (links.map (replaceText text)).map Prod.fst = links.map Prod.fst := by
    simp [List.map_map, Function.comp_def, replaceText]
  refine ⟨by simpa using nonempty, order ▸ distinct, ?_, ?_, transfer_justification same enough,
    order ▸ neighbors, transfer_keys keep keyed, inQ, inA, ?_⟩
  · intro l member
    obtain ⟨orig, hl, rfl⟩ := List.mem_map.mp member
    exact represented orig hl
  · intro pre l post split
    obtain ⟨before, rest, shape, rfl, middle⟩ := List.map_eq_append_iff.mp split
    obtain ⟨orig, after, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp middle
    obtain ⟨rule, evaluates⟩ := p5
    let meaning (z : Link T F) := (z.1, z.2.textContent)
    have unchanged (z : Link T F) (hz : z ∈ links) : meaning (replaceText text z) = meaning z :=
      Prod.ext rfl (same z hz)
    have mapped (part : List (Link T F)) (included : part ⊆ links) :
        (part.map (replaceText text)).map meaning = part.map meaning := by
      rw [List.map_map]
      exact List.map_congr_left (fun z hz => unchanged z (included hz))
    have beforeEq := mapped before (fun _ hz => shape ▸ List.mem_append_left _ hz)
    have middleEq := unchanged orig (by simp [shape])
    have afterEq := mapped after (fun _ hz => shape ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hz))
    apply (evaluates _ _ _ (Or.inr split)).2
    change rule _ (meaning (replaceText text orig)) _
    rw [beforeEq, middleEq, afterEq]
    exact (evaluates before orig after (Or.inl shape)).1 (contributes before orig after shape)
  · obtain ⟨l, hl, designated⟩ := common
    exact ⟨replaceText text l, List.mem_map.mpr ⟨l, hl, rfl⟩, designated⟩

/-- Полные новые тексты дают первый вариант HasOrigin; для сокращённых
проверяется путь нового набора со всеми прежними ключами. -/
theorem transfer_supports {Q : String} {a : T.Content} {links : List (Link T F)}
    {keys : List T.Obj} {o : T.Obj} {text : F → Reading T} (old : M.Supports E Q a links keys o)
    (same : SamePresentedContent M text links)
    (p5 : ContributionByContent M Q a links (links.map (replaceText text)))
    (keep : RetainsKeys M text links keys)
    (common : ∃ l ∈ links, M.presentation.Designates (text l.1) o)
    (origin : M.HasOrigin E Q a (links.map (replaceText text)) keys o) :
    M.Supports E Q a (links.map (replaceText text)) keys o :=
  ChainModel.supports_iff_now_and_origin.mpr ⟨transfer_supports_now old same p5 keep common, origin⟩

/-- После переноса берём минимум среди совместимых сокращений именно
нового набора. Основания, ключи переходов и общий объект сохраняются. -/
theorem minimize_transferred {Q : String} {a : T.Content} {links : List (Link T F)}
    {text : F → Reading T} {keys : List T.Obj} {o : T.Obj}
    (checked : M.Supports E Q a (links.map (replaceText text)) keys o) :
    ∃ best, Edits (Section04.TupleCut E Q a keys o) (links.map (replaceText text)) best ∧
      best.map Prod.fst = links.map Prod.fst ∧
      (∀ other, Edits (Section04.TupleCut E Q a keys o) (links.map (replaceText text)) other →
        Section04.totalTextLength best ≤ Section04.totalTextLength other) ∧
      M.Supports E Q a best keys o ∧ M.Admissible E Q a best o := by
  obtain ⟨best, reached, order, least, supported, minimal⟩ := Section04.minimize_tuple checked
  exact ⟨best, reached, by simpa [List.map_map, Function.comp_def, replaceText] using order,
    least, supported, minimal⟩

#print axioms transfer_justification
#print axioms transfer_keys
#print axioms transfer_supports
#print axioms minimize_transferred

end SemanticChains.Section06
