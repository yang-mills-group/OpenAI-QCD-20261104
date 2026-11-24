import YM.Infer.Shack
import YM.Pods.Atlases
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise ContDiff Stamp Kronecker Classical
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Gallery
open QCD.Kites PrismD Civic
open Romance
local notation "V"=> Lat.Fields n 6
local notation "Fω"=> Insertion n 6
variable {p:Label d}(Y: SourceRead.TaperHol)(W:Knot p)(h:Requisite Y p W)
open Patria Patria.Depth Patria.Hub
-- source-independent geometry Κ bounds. sym parity.
lemma caseFoot {Vb:Source.Hol su}(Uv:Lining.Temper.Collage.Exhibit Vb)(d:ℕ): ∃ r:ℕ,∀ (n:Side)(o:Cover)(x:Label d), Floors (rim r (wrap n o)) (Bloom Uv d n o x):=by obtain ⟨k,h⟩:= shafts (Uv.t d); exact ⟨k,fun n o x=> Romance.houses (Uv.t d) o _ (h n o) _ (Uv.lead d x) (fun _=>rfl)⟩
include h
structure ReachV {Vb:Source.Hol su} (U:Lining.Temper.Collage.Exhibit Vb) (Z r:ℕ) : Prop where
    wide (l:List Axis): l.length≤Z→∀ (n:Side)(P: Regulator n 6)(O:BudgetPoint)(v:ℝ)(b:Cover), Floors (rim r (wrap n b)) (poseEye W P O v l n b)
    useN : ∀ (n:Side)(o:Cover)(x:Label d), Floors (rim r (wrap n o)) (Bloom U d n o x)
#check ReachV
lemma brakeW {Vb:Source.Hol su}(Uv:Lining.Temper.Collage.Exhibit Vb) (Z:ℕ): ∃ k:ℕ, ReachV W Uv Z k:=by obtain ⟨r,hr⟩:= shutters Y W h Z; obtain ⟨u,hu⟩:= caseFoot Uv d; exact ⟨r+u,⟨fun l hv n P O v b=> RP.lower_maps (hr l hv n P O v b) (fun z hz=>Nat.le_trans hz (Nat.le_add_right ..)),fun n o x=>RP.lower_maps (hu n o x) (fun z hz=>Nat.le_trans hz (Nat.le_add_left ..))⟩⟩
end Gallery
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.Gallery.brakeW
