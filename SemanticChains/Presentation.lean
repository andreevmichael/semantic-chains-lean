/-! Обозначения для формулировки теоремы: представления, пути и сокращения. -/
namespace SemanticChains

/-- An edge witness identifies a particular occurrence of a child in a
full representation of its parent. The general proof uses two consequences
of P2: expansion yields a full parent representation and preserves the child's
verified object designations. In the positive registry (§5.2), Context.fill
implements substitution at the selected position, and local_expansion proves
that this substitution preserves the parent's full content.
Text may be a string template or an address-verified reading in a contract. -/
structure Presentation (Fact Obj : Type) (Text : Type := String) where
  Occurrence : Fact → Fact → Type
  Full : Fact → Text → Prop
  Designates : Text → Obj → Prop
  expand : {p c : Fact} → Occurrence p c → Text → Text
  full_expand : ∀ {p c : Fact} (w : Occurrence p c) {v : Text},
    Full c v → Full p (expand w v)
  retains_designation : ∀ {p c : Fact} (w : Occurrence p c) {v : Text} {o : Obj},
    Full c v → Designates v o → Designates (expand w v) o

/-- The path goes from parent to child and records the witness at every step. -/
inductive Path {Fact : Type} (Occurrence : Fact → Fact → Type) : Fact → Fact → Type where
  | here (f : Fact) : Path Occurrence f f
  | step {p c f : Fact} :
      Occurrence p c → Path Occurrence c f → Path Occurrence p f

/-- Вершины пути, включая оба конца. -/
def Path.vertices {Fact : Type} {R : Fact → Fact → Type} {p f : Fact} :
    Path R p f → List Fact
  | .here x => [x]
  | .step (p := x) _ tail => x :: Path.vertices tail

/-- Finite sequences of edits of one text (§4.2) or a tuple of texts (§4.4). -/
inductive Edits {α : Type} (step : α → α → Prop) (start : α) : α → Prop where
  | refl : Edits step start start
  | snoc {u v : α} : Edits step start u → step u v → Edits step start v

end SemanticChains
