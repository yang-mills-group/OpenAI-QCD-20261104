import YM.Tarn.Spoil
/-! Underlying exact torus laws on arbitrary order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Dispersed
open Function QCD QCD.Lat QCD.RP QCD.Tide Lyre Grass Wilson Patria Patria.Depth Patria.Hub Lattice Cylinder
open TorusPCAC.Geometry TorusPCAC.Geometry.AxisB MeasureTheory Massive.UV
open scoped Topology BigOperators Classical
variable {n:Side} (R:Regulator n 6) (hr:R.t=0)
local notation "Gₙ"=> Grid n
local notation "W"=> R.density

local notation "Ω"=> n
local notation "E"=> Lat.Fields Ω 6
local notation "μ"=> prior su n
local notation "b"=> ber (Modes n 6)
variable {I:Type*} 
namespace MoveR
-- orientation complex-linear. One API with local measure preservation. p receipts broaden. words
structure Crest (F: Massive.Density n 6 → Density n 6) where
    A : Grid n → Grid n
    M : Lat.Fields n 6 →ₐ[ℂ] Lat.Fields n 6
    act (f:Density n 6)(U:Gₙ):F f U=M (f (A U))
    preserves:MeasurePreserving A μ μ
    holds:F W=W
    sees (u:E): ber (Modes n 6) (M u)= ber (Modes n 6) u
namespace Crest
-- normalized expectation invariance
variable {R} -- bad
variable {F:Density n 6→ Density n 6} (K:Crest R F)
include K
lemma uses (X Y: Insertion n 6)(h:⇑Y= F X):R.average Y=R.average X:=by
    suffices hh:R.raw Y=R.raw X by unfold Regulator.average; simp[hh]
    change joint _=joint _; unfold joint; let U(V:Gₙ):ℂ:=b ((W*X) V); have hx:(fun V=> b ((W*Y) V))=fun V=> U (K.A V):=by
         funext z; simp only[ContinuousMap.mul_apply,h, K.act]; rw [show W z=_ from (congr_fun K.holds z).symm.trans (K.act W z),← map_mul]; exact K.sees _ -- argument? congr symmetry likely
    have hk:=K.preserves; rw [hx, ← integral_map hk.aemeasurable (hk.map_eq.symm ▸ (show Integrable U μ from R.integrable X).aestronglyMeasurable),hk.map_eq]
lemma skies(L:List I)(x y:I→ Insertion n 6)(h:∀ i: I, i∈L → F ⇑(x i)= y i): R.average (L.map y).prod=R.average (L.map x).prod:=by
    apply K.uses; funext z; rw [K.act]; change (L.map y).prod z=K.M ((L.map x).prod (K.A z)); induction L with
    | nil=> rw [List.map_nil,List.map_nil,List.prod_nil]; change (1:E)=K.M 1; rw [map_one]
    | cons j l ih=>
        simp only[List.map_cons,List.prod_cons,ContinuousMap.mul_apply]; rw [map_mul, ih (fun i hi=>h _ (List.mem_cons_of_mem _ hi)),show y j z=_ from (congr_fun (h j (List.mem_cons_self ..)) z).symm.trans (K.act ..)]
end Crest
open TorusPCAC.Ward
variable (p:EuPin)(s:Signed)(h:p.Lifts s)(u:FlavorTorus)
lemma flavorP :Nonempty (Crest R (Action.flavor u)):=by
    let g:= Exposure.proclaim u; refine ⟨⟨id, TorusPCAC.Ward.acts g n, fun X z=> congr_fun (Exposure.flavor_show ..) z, MeasurePreserving.id μ, Exposure.flavor_pivot R u,fun x=> Kit.vanishV (tag_unit _) _⟩⟩ -- signatures
lemma chargeP :Nonempty (Crest R Action.charge):=by
    refine ⟨⟨TorusPCAC.Stencil.conjGrid,TorusPCAC.Stencil.charge n,fun X z=> congr_fun (Exposure.charge_west X) z,Reflection.grid_preserve,Exposure.charge_pivot R,fun x=>?_⟩⟩
    unfold TorusPCAC.Stencil.charge; rw [shifted]; exact Switch.volume _ _ (pay _ _ TorusPCAC.Jet.Selector.pays_C) _ -- pays_C namespace
lemma parityP : Nonempty (Crest R Action.parity) :=by
    refine ⟨⟨id, Grass.grade,fun _ _=>rfl,MeasurePreserving.id μ,?_,fun x=> TorusPCAC.Finite.vol_grade x⟩⟩
    funext i; change grade (W i)=W i; rw[Regulator.density_apply,map_smul]; exact congr_arg _ (gauss_plus (R.D i)) -- expects Plus.C
include hr h in
lemma pinP : Nonempty (Crest R (Action.pin p s)) :=by
    refine ⟨⟨pull s 0,crank s p.matrix.val 0 (Patria.prism s),fun F U=> congr_fun (pinned ..) U,prior_pull .., Exposure.pin_pivot s p R h hr,fun x=>?_⟩⟩
    have he:= QCD.Revolve.colour_wheel (smoke (c:=n) s) (EuPin.retains s h); exact Kit.vanishV (copies_unitary _ _ he) x
include hr
lemma marchP(x:Cover):Nonempty (Crest R (march x)):=by
    let g:=heat (n:=n) x; refine ⟨⟨pull 1 (wrap n x),crank 1 1 _ g,fun _ _=>rfl,prior_pull .., Exposure.move_pivot R x hr,fun V=>?_⟩⟩; exact Kit.vanishV (copies_unitary _ _ (QCD.Revolve.colour_wheel (glares _) QCD.Revolve.Swing.none)) _
end MoveR
end YM.Massive.Tarn.Dispersed
#print axioms YM.Massive.Tarn.Dispersed.MoveR.Crest.skies
