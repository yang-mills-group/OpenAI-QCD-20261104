import YM.Patria.Pilot
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
namespace Depth
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
open Poised Poised.Plans Poised.Display
variable {c:Side}{d:ℕ}(X Y P:Density c 6)(x y:Label d)(H: SourceRead.TaperHol)(b:Cover)
-- Tally linear.
local notation "V"=> Canvas.foil P
lemma tally_sub (h:Tally H b x P X)(hp:Tally H b y P Y) : Tally H b (x-y) P (X-Y):=by
    have he:= Orientation.acting H b d (V Y) y.val hp.sees (-1:ℂ); rw [neg_one_smul, show ((-1:ℂ) • y.val)= -y.val from neg_one_smul ℂ y.val] at he
    refine ⟨h.unit,?_⟩; have hP:= Orientation.actsPlus H b d (V X) (-(V Y)) x.val (-y.val) h.sees he; change Beacon.ActionTest H b (V (X-Y)) (x.val-y.val); rw [sub_eq_add_neg (x.val), show V (X-Y)=V X+ -(V Y) from (by funext U; simp [Canvas.foil,sub_eq_add_neg,mul_add])]; exact hP
-- BP Cayley arrays
variable {S: Scheme}{N m:ℕ}{r:Side}(A:Run S N r 6)(F G:Cover→ Insertion (S.side r N) 6)(u:Averaging)(i:ℕ)
local notation "Tp" F:arg => trolley A F u
local notation "Z"=> Insertion (S.side r N) 6
lemma truck_plus : trolley A (F+G) u i b=trolley A F u i b+trolley A G u i b:=by
    unfold trolley visitor; simp_rw [Rolls.roles]; rw [Rolls.training]; simp only [Pi.add_apply,mul_add,map_add]
lemma truck_sub : trolley A (F-G) u i b=trolley A F u i b-trolley A G u i b:=by apply eq_sub_of_add_eq; rw [←truck_plus]; rw [sub_add_cancel]
lemma postcard (h:∀ a b,march b (F a)=F (a+b))(hv:∀ a b,march b (G a)=G (a+b)) (a b:Cover): march b ((F-G) a)= (F-G) (a+b):=by funext V'; let D:= TorusPCAC.Geometry.crank 1 1 (wrap (S.side r N) b) (TorusPCAC.Geometry.heat b) (N:=6); exact (map_sub D _ _).trans (congr_arg₂ Sub.sub (congr_fun (h ..) V') (congr_fun (hv ..) V'))
end Depth
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Depth.tally_sub
#print axioms YM.Massive.Patria.Depth.truck_sub
