import YM.QCD.Fold.Mesh
import YM.QCD.Villa.Glow
/-! # issue physical and test reprint packs. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open Bay Strut Sway Revolve Quarry Port RG Leaf Tee LeafM Rudder Eyrie Sparks Garden YM.Next.Free
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{D b B j k x χ:ℕ}(X: Flight j k){e : f.val=c.val*X.L.val}{E:F.val=C.val*X.L.val}(h:C.val=c.val*D)(hl:2≤c.val)
variable (d:Site F→ℂ)(hd:Quaint (Lace.project (P:=X.patch) (h:=e) (H:=E) h hl).high d)
local notation "V"=> Lace.project (P:=X.patch) (h:=e) (H:=E) h hl
local notation "r"=>sliceL X e
local notation "R"=>sliceL X E
variable {Q:Plan j}{P:Plan k}{t z a p A m q w u η p' z' A' Ω Ω' ℓ:ℝ}{Z : Offer 1 t p}{U':Offer 2 a A}{J:ℕ→Atom su 2}
include hd
lemma consumes (hv:Species X E w p' z' η A' x (park X E Q Z U' z m))(hp:Species X e w p' z' η A' x (park X e Q Z U' z m))(hT:0<t)(hA:0<a)(hz:0<z)(hq:z≤1):Collum.Receives (pressL (X:= X.patch) (e:=e) (E:=E) h hl d) (dusk X E P (park X E Q Z U' z m)) (dusk X e P (park X e Q Z U' z m)):=by
   have hh:=descend X V hd; refine ⟨(V).low.fold,fun i=>?_,fun U i j=>rule _ _ hh _ _ (kiosk X h hl d hd hv hp hT hA hz hq U) i j⟩; rcases hh.sign i with b|b <;> change ‖(d ∘ (V).R.embed) i‖=_<;>rw[b]<;>simp
variable (Y: Swathe X E (park X E Q Z U' z m) J P w z' η Ω Ω' b)
local notation "Q'"=> pressL (X:=X.patch) (E:=E) (e:=e) h hl d
local notation "A'"=> anchL (X:=X.patch) (E:=E) (e:=e) h hl d -- shadows real
lemma onboard (hv:Species X E w p' z' η ℓ x (park X E Q Z U' z m))(hp:Species X e w p' z' η ℓ x (park X e Q Z U' z m))(hT:0<t)(hA:0<a)(hz:0<z)(hq:z≤1)(B:ℕ)(hB:4*B+3<f.val)(hr:0≤η):
   ∃ S:Swathe X e (park X e Q Z U' z m) J P w z' η Ω Ω' b,S.bath=(Q').cloud Y.bath b B ∧ S.walk=(A').cloud Y.walk b B:=by
   have hx := consumes (P:=P) X h hl d hd hv hp hT hA hz hq; have hf:= line_support (X:=X.patch) h hl d hd (fun i=> probed X h hl d hd hv hp hT hA hz hq i J)
   have he := (Q').holds Y.glow (A:=dot r) (fun u k T hk=> by obtain ⟨w,l,hw,-,ht⟩:= issues (X:=X.patch) h hl d hd u k T hk; exact ⟨w,l,hw,ht⟩) b B
   have hh := (A').holds Y.puff (A:=sun r) (fun u k T hk=> by obtain ⟨w,l,hw,ht,-⟩:= issues (X:=X.patch) h hl d hd u k T hk; exact ⟨w,l,hw,ht⟩) b B
   exact ⟨⟨_,_, (Q').plates _ _ _ _ Y.arcP hB hx hr,he,(Q').wax b B _ Y.germ,_,_,(A').plates _ _ _ _ Y.att hB hf hr,hh⟩,rfl,rfl⟩
end YM.QCD.Folding
#print axioms YM.QCD.Folding.onboard
