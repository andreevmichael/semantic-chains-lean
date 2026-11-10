import SemanticChains.ContractGraph

/-! Формулировка основной теоремы, до доказательства (§§1–4).
Q и A — строки, Â — восстановленное логическое содержание. Все обозначения
относятся к одному состоянию контракта. -/

namespace SemanticChains

open LemmaOne (State Anchored FullAnswer InQuestion InFullAnswer)

abbrev Link (T : State) (Fact : Type) := Fact × Reading T

/-- Интерпретация обозначений статьи. П1–П2 заданы в Presentation.
Условия о полном тексте применяются к любому его лексическому предъявлению.
Предикат вклада проверяется в окружении остальных звеньев (П5). -/
structure ChainModel (T : State) (Fact I : Type) where
  registered : List Fact
  presentation : Presentation Fact T.Obj (Reading T)
  factContent : Fact → T.Content
  graph : ContractGraph T presentation registered factContent
  /-- П1: для обозначенного в факте объекта можно выбрать полный текст,
  сохраняющий его обозначение. Он может отличаться от зафиксированной записи. -/
  full_for_recorded_object : ∀ {f o}, graph.RecordedObject f o →
    ∃ v, presentation.Full f v ∧ presentation.Designates v o
  holds : T.Content → I → Prop
  preservation_sound : ∀ {p c}, graph.preserves p c → ∀ i, holds (factContent p) i → holds (factContent c) i
  full_iff : ∀ {f v}, presentation.Full f v ↔ v.textContent = factContent f
  /-- Обозначение факта и его роль по адресу в тексте вопроса (К1.1). -/
  questionFactMention : String → T.Occ → Option (String × T.Role)
  expresses : String → T.Content → Fact → Prop
  contributes : String → T.Content → List (Link T Fact) → Link T Fact → List (Link T Fact) → Prop
  full_contributes : ∀ {Q a f v}, expresses Q a f → presentation.Full f v →
    contributes Q a [] (f, v) []
  /-- Содержательная часть П3: сохранены статус, роли и необходимые условия. -/
  faithfulEdit : Fact → Reading T → Reading T → Prop

/-- Выбираются только засвидетельствованные вхождения в контракте.
chosen позволяет различить несколько вхождений одного подфакта. -/
structure Expansion {T : State} {Fact I : Type} (M : ChainModel T Fact I) where
  root : Fact
  chosen : {p c : Fact} → M.presentation.Occurrence p c → Prop

namespace Expansion

variable {T : State} {Fact I : Type} {M : ChainModel T Fact I}

def Edge (E : Expansion M) (p c : Fact) :=
  {w : M.graph.Edge p c // E.chosen w.val}

def InS (E : Expansion M) (f : Fact) : Prop := Nonempty (Path E.Edge E.root f)

/-- Подъём от x к pivot и спуск к y. При двух непустых ветвях проверяем
роли в общем родителе. Полный путь проходит через каждую вершину один раз. -/
def Connected (E : Expansion M) (x y : Fact) : Prop :=
  ∃ pivot, E.InS pivot ∧
    ∃ (left : Path E.Edge pivot x) (right : Path E.Edge pivot y),
      ((Path.vertices left).reverse ++ (Path.vertices right).tail).Nodup ∧
      (match left, right with
       | .step wl _, .step wr _ => M.graph.CommonRelation wl.val.val wr.val.val
       | _, _ => True)

end Expansion

namespace ChainModel

variable {T : State} {Fact I : Type}

theorem full_content {M : ChainModel T Fact I} {f v} (h : M.presentation.Full f v) :
    v.textContent = M.factContent f := M.full_iff.mp h

theorem same_fact_of_full_readings {M : ChainModel T Fact I} {f g v u}
    (hf : f ∈ M.registered) (hg : g ∈ M.registered)
    (fv : M.presentation.Full f v) (gu : M.presentation.Full g u)
    (address : v.address = u.address) (wording : v.wording = u.wording) : f = g :=
  M.graph.identity_of_content hf hg ((M.full_content fv).symm.trans
    ((Reading.unique address wording).trans (M.full_content gu)))

def Entails (M : ChainModel T Fact I) (premise conclusion : T.Content) : Prop :=
  ∀ i, M.holds premise i → M.holds conclusion i

/-- §1.1: проверка возможного основания в выбранном состоянии контракта.
expresses учитывает запрошенное отношение с его участниками, ролями и
условиями. Обоснованность полного ответа проверяется отдельно. -/
structure PossibleRoot (M : ChainModel T Fact I) (Q : String) (a : T.Content)
    (r : Fact) : Prop where
  registered : r ∈ M.registered
  expresses : M.expresses Q a r
  justifies : M.Entails (M.factContent r) a

def Cut (M : ChainModel T Fact I) (f : Fact) (v u : Reading T) : Prop :=
  M.faithfulEdit f v u ∧ M.Entails v.textContent u.textContent ∧
    u.wording.length < v.wording.length

/-- Один объект на переход. Концы — вопрос и полное содержание ответа.
Внутренние звенья предъявляют оба своих ключа в одном и том же тексте. -/
def keyed : List (T.Obj → Prop) → List T.Obj → Prop
  | [_], [] => True
  | left :: right :: rest, o :: keys => left o ∧ right o ∧ keyed (right :: rest) keys
  | _, _ => False

def adjacent (rel : Fact → Fact → Prop) : List Fact → Prop
  | x :: y :: rest => rel x y ∧ adjacent rel (y :: rest)
  | _ => True

/-- Совместная проверка одного упорядоченного набора текстов (П1–П5, С1–С6).
Обозначения считаются проверенными в фиксированном контракте. -/
def SupportsNow (M : ChainModel T Fact I) (E : Expansion M) (Q : String) (a : T.Content)
    (links : List (Link T Fact)) (keys : List T.Obj) (common : T.Obj) : Prop :=
  links ≠ [] ∧ (links.map Prod.fst).Nodup ∧
  (∀ l ∈ links, E.InS l.1) ∧
  (∀ pre l post, links = pre ++ l :: post → M.contributes Q a pre l post) ∧
  (∀ i, (∀ l ∈ links, M.holds l.2.textContent i) → M.holds a i) ∧
  adjacent E.Connected (links.map Prod.fst) ∧
  keyed (InQuestion T Q :: links.map (fun l => M.presentation.Designates l.2) ++
    [InFullAnswer T a]) keys ∧
  InQuestion T Q common ∧ InFullAnswer T a common ∧
  ∃ l ∈ links, M.presentation.Designates l.2 common

/-- П3: от полного совместимого набора меняется один текст за шаг.
Основания, вопрос, ответ и все ключи фиксированы на всём пути. -/
inductive Supports (M : ChainModel T Fact I) (E : Expansion M) (Q : String) (a : T.Content) :
    List (Link T Fact) → List T.Obj → T.Obj → Prop where
  | full {links keys o} : (∀ l ∈ links, M.presentation.Full l.1 l.2) →
      M.SupportsNow E Q a links keys o → Supports M E Q a links keys o
  | shorten {pre post f v u keys o} :
      Supports M E Q a (pre ++ (f, v) :: post) keys o → M.Cut f v u →
      M.SupportsNow E Q a (pre ++ (f, u) :: post) keys o →
      Supports M E Q a (pre ++ (f, u) :: post) keys o

theorem Supports.now {M : ChainModel T Fact I} {E Q a links keys o}
    (h : M.Supports E Q a links keys o) : M.SupportsNow E Q a links keys o := by
  cases h with
  | full _ ok | shorten _ _ ok => exact ok

/-- Происхождение предъявленного набора до проверки его текущего состояния.
Либо все тексты полны, либо известен один последний Cut из уже проверенного набора. -/
def HasOrigin (M : ChainModel T Fact I) (E : Expansion M) (Q : String) (a : T.Content)
    (links : List (Link T Fact)) (keys : List T.Obj) (o : T.Obj) : Prop :=
  (∀ l ∈ links, M.presentation.Full l.1 l.2) ∨
    ∃ pre post f v u, links = pre ++ (f, u) :: post ∧
      M.Supports E Q a (pre ++ (f, v) :: post) keys o ∧ M.Cut f v u

theorem supports_iff_now_and_origin {M : ChainModel T Fact I} {E Q a links keys o} :
    M.Supports E Q a links keys o ↔ M.SupportsNow E Q a links keys o ∧ M.HasOrigin E Q a links keys o := by
  constructor
  · intro path
    refine ⟨path.now, ?_⟩
    cases path with
    | full valid _ => exact Or.inl valid
    | shorten prev cut _ => exact Or.inr ⟨_, _, _, _, _, rfl, prev, cut⟩
  · rintro ⟨now, full | ⟨pre, post, f, v, u, rfl, prev, cut⟩⟩
    · exact .full full now
    · exact .shorten prev cut now

/-- Членство в 𝒢. При проверке минимальности текста одного звена остальные
звенья, факты-основания и объекты переходов фиксированы (П3, П6). -/
def Admissible (M : ChainModel T Fact I) (E : Expansion M) (Q : String) (a : T.Content)
    (links : List (Link T Fact)) (o : T.Obj) : Prop :=
  ∃ keys, M.Supports E Q a links keys o ∧
    ∀ pre f v post u, links = pre ++ (f, v) :: post → M.Cut f v u →
      ¬ M.SupportsNow E Q a (pre ++ (f, u) :: post) keys o

end ChainModel

/-- Цель доказательства. r выражает запрошенное отношение и обосновывает Â.
В выбранном раскрытии r предъявлен носитель общего объекта. Обнаружимость
корня и включение S ⊆ W будут результатами §3. -/
def MainTheorem {T : State} {Fact I : Type} (M : ChainModel T Fact I) : Prop :=
  ∀ (Q A : String) (a : T.Content) (E : Expansion M),
    Anchored T Q → FullAnswer T Q A a →
    M.PossibleRoot Q a E.root →
    (∃ f o, E.InS f ∧ M.graph.RecordedObject f o ∧
      InQuestion T Q o ∧ InFullAnswer T a o) →
    ∃ (links : List (Link T Fact)) (o : T.Obj), M.Admissible E Q a links o

end SemanticChains
