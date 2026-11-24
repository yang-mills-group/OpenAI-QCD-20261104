import YM.Sprig.Roof
set_option autoImplicit false
noncomputable section
namespace YM.Sprig.Chloe
open Massive Function Filter Matrix Set Finset QCD QCD.Lat QCD.Grass QCD.Creek Lattice Wilson MeasureTheory
open scoped BigOperators Topology Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ComplexOrder Kronecker
variable {A: Massive.Sequence}(P: Calibration A) {d:ℕ}
open UV Cylinder Patria Patria.Depth
open Patria.Exposure
variable (n:Side)(x y: Massive.UV.Label d)

variable (h: P.System)
open TorusPCAC.Geometry TorusPCAC.Geometry.AxisB TorusPCAC.Geometry.Switch TorusPCAC.Ward TorusPCAC.Jet TorusPCAC.Jet.Selector QCD.Revolve
theorem passage (H:Grid n→ Grid n)(he:MeasurePreserving H (prior su n) (prior su n)) : (∫ U,costH P n x y (H U) ∂(prior su n))=pollen P n x y:=by unfold pollen; rw [← integral_map he.aemeasurable (he.map_eq.symm ▸ (earnH P n x y).aestronglyMeasurable),he.map_eq]
include h
theorem gloss : pollen P n (P.sym.charge d x) (P.sym.charge d y)=pollen P n x y:=by
     let Q:=TorusPCAC.Stencil.conjGrid (n:=n); rw [← passage P n x y Q Reflection.grid_preserve]; unfold pollen; let M:= Cmat; let G:=Jobs n 6 M; let N:=Jobs n 6 M⁻¹; have hm:G∈unitary _:=frameC ..
     have hN :N∈unitary _:=by
          have he:N=star G:=Eq.symm (Eq.trans (drum _) (congr_arg (Jobs n 6) (show star Cmat=Cmat⁻¹ from (by rw[inverse_C]; unfold Cmat; rw[star_mul,gamma_star,gamma_star])))); rw [he]; exact Unitary.star_mem hm
     apply integral_congr_ae; filter_upwards with U
     let B:=P.candidate d n 0; have hp (p:Massive.UV.Label d): B ( (P.sym.charge d)  p) U= shiftC G N (B p (Q U)):=by
         rw [show B _ _= _ from (congr_fun (h.sections.charge d n 0 p) U).symm,charge_west]; unfold TorusPCAC.Stencil.charge; exact shifted ..
     unfold costH; change poly (B _ _) (B _ _)=_; rw [hp,hp]; exact baseCharge _ _ hm hN
theorem brood (p:EuPin)(s:Signed)(ht:p.Lifts s): pollen P n (P.sym.pin d p x) (P.sym.pin d p y)=pollen P n x y:=by
    let Q:= pull (K:=su.El) s (0:Site n); rw [← passage P n x y Q (prior_pull ..)]; unfold pollen; apply integral_congr_ae; filter_upwards with U; let B:=P.candidate d n 0; let v:= copies 6 (hues (0:Site n) s (Patria.prism s) p.matrix.val)
    have hp(a:Massive.UV.Label d):B (P.sym.pin d p a) U= Kit.disguise v (B a (Q U)):=by have he:= h.sections.pin d n 0 a p s ht; rw [Signed.act_zero,Patria.pinned] at he; exact (congr_fun he U).symm
    unfold costH; change poly (B _ _) (B _ _)=_; rw[hp,hp]; exact costume _ _ (copies_unitary _ _ (colour_wheel (smoke (c:=n) s) (EuPin.retains s ht)))
theorem figurine(a:Axis):pollen P n (P.sym.adj d a x) (P.sym.adj d a y)=star (pollen P n x y):=by
    let s:= Signed.mirror a; let Q:= pull (K:=su.El) s (0:Site n); let H:= (prior_pull (t:=(0:Site n)) (s:=s) (G:=su)); rw [sparks, ← passage P n y x Q H]; unfold pollen; apply integral_congr_ae; filter_upwards with U; let B:=P.candidate d n 0
    have hp(p:Massive.UV.Label d):B (P.sym.adj d a p) U=Grass.tilt (eyeP n a) (B p (Q U)):=by have he:= h.sections.star d n 0 p a; rw [Signed.act_zero] at he; exact (congr_fun he U).symm.trans (eye_value ..)
    unfold costH; change poly (B _ _) (B _ _)=_; rw [hp,hp,litP _ _ (eye_unit a),sun]
theorem fauna(u:FlavorTorus):pollen P n (P.sym.flavor d u x) (P.sym.flavor d u y)=pollen P n x y:=by
    unfold pollen; apply integral_congr_ae; filter_upwards with z
    let B:=P.candidate d n 0; let t:= TorusPCAC.Ward.tag n (proclaim u)
    have hp(p:Massive.UV.Label d):B (P.sym.flavor d u p) z= Kit.disguise t (B p z):=by have he:=h.sections.flavor d n 0 p u; rw [flavor_show] at he; exact (congr_fun he z).symm
    unfold costH; change poly (B _ _) (B _ _)= _; rw [hp,hp]; exact costume _ _ (tag_unit _)
theorem parityE:pollen P n (P.sym.parity d x) (P.sym.parity d y)=pollen P n x y:=by
    unfold pollen; apply integral_congr_ae; filter_upwards with z; let B:= P.candidate d n 0
    have hp(p:Massive.UV.Label d):B (P.sym.parity d p) z= Grass.grade (B p z):= (congr_fun (h.sections.parity d n 0 p) z).symm
    unfold costH; change poly (B _ _) (B _ _)=_; rw [hp,hp]; exact gradeSum _ _
end YM.Sprig.Chloe
#print axioms YM.Sprig.Chloe.frameC
#print axioms YM.Sprig.Chloe.figurine
#print axioms YM.Sprig.Chloe.gloss
#print axioms YM.Sprig.Chloe.ppU
#print axioms YM.Sprig.Chloe.brood
