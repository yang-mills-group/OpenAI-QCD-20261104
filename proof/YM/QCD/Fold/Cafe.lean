import YM.QCD.Fold.Ice
/-! # Trainers & rites auxiliary tags -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open Bay Strut Sway Revolve Quarry Port RG Leaf Tee LeafM Rudder Eyrie Sparks Garden YM.Next.Free Loom
open Cove Grass
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{D b B j k x χ N:ℕ}
section alone
variable {L:Window c C D}(d:c.val ∣ C.val)(h:L.cut=(⇑(splitter d)))(p:Site C→ℂ)(hp:Quaint L p)
open Villa Pine
variable {W:Land C (Site C) (Site C)}{Y:Pays C (Site C) (Site C)}{Q:Plan k}{Z:Train k}{a t w :ℝ}
include hp
lemma tramples (hf:Run.Pack id id a t b (wood Q 0 Z) w W Y)(hW:Torch W)(ha:0 < a)(hv:4*B+3<c.val)(U: Grid c)(x:Site C):
   batch (singleR c) ((deck L d h p).cloud W b B) (L.cut x) none B (settled U)= (stream L p)ᴴ* batch (singleR C) W x none B (settled (L.links U))* stream L p:= forge (deck L d h p) L (needed L d h p hp Q Z) hf hW.1 (litter L d h p hp) hv _ _ rfl (fun i=>Eq.symm (monotype i)) (fun i=>Eq.symm (monotype i)) U x ha
end alone
variable (X: Flight j k){e : f.val=c.val*X.L.val}{E:F.val=C.val*X.L.val}(h:C.val=c.val*D)(hl:2≤c.val)
variable (d:Site F→ℂ)(hd:Quaint (Lace.project (P:=X.patch) (h:=e) (H:=E) h hl).high d)
local notation "V"=> Lace.project (P:=X.patch) (h:=e) (H:=E) h hl
local notation "r"=>sliceL X e
local notation "R"=>sliceL X E
variable {W:Land C (Site C) (Site C)}{Y:Pays C (Site C) (Site C)}{Q:Plan k}{Z:Train k}{a t w :ℝ}
open Villa Pine
set_option quotPrecheck false
local notation "Θ"=> deck (V).low (divides h) rfl (d ∘ (R).embed)
include hd
lemma breakfast (hf:Run.Pack id id a t b (wood Q 0 Z) w W Y)(hW:Torch W)(ha:0 < a)(hv:4*B+3<c.val)(U: Grid f)(V':Grid c)(x:Site C)(N:ℕ):
    axes (V).low (d ∘ (R).embed) N (dropG N W R B (x,none) ((V).high.links U) ((V).low.links V'))=dropG N ((Θ).cloud W b B) r B ((V).low.cut x,none) U V':=by
    unfold dropG sheetP; dsimp only
    have H : Quaint (V).low (d∘(R).embed) := descend X V hd
    rw [carry_ψ, Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_sub,Matrix.sub_mul,dips X h hl]
    rw [← tramples (divides h) rfl _ H hf hW ha hv V' x, ← tramples (divides h) rfl _ H hf hW ha hv _ x]
end YM.QCD.Folding
#print axioms YM.QCD.Folding.bath_ψ
#print axioms YM.QCD.Folding.breakfast
