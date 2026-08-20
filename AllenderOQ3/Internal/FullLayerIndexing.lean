import AllenderOQ3.Incidence

set_option autoImplicit false
set_option linter.unusedVariables false

namespace AllenderOQ3.Internal

variable {n : Nat} (c : ADRCircuit n)

def subtypeUnivEquiv {α : Type} {p : α → Prop} (h : ∀ x, p x) : α ≃ { x // p x } where
  toFun x := ⟨x, h x⟩
  invFun x := x.1
  left_inv x := rfl
  right_inv x := rfl

/-- A bijection between the vertices of layer `ell` and their indices in the certificate's layer
  order. -/
noncomputable def FullLayerIndexing (cert : IncidenceCylinder c) (ell : Nat) :
    LayerVertex c ell ≃ Fin (cert.layerOrder ell).entries.length :=
  let l := (cert.layerOrder ell).entries
  let H := (cert.layerOrder ell).nodup
  have heq : LayerVertex c ell ≃ { x : LayerVertex c ell // x ∈ l } :=
    subtypeUnivEquiv (cert.layerOrder ell).complete
  heq.trans (List.Nodup.getEquiv l H).symm

end AllenderOQ3.Internal
