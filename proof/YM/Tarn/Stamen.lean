import YM.Tarn.Nacre
/-! Torus Euclidean adjoint: reverse ANY list; this needn't be on one side. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Dispersed
open Function QCD QCD.Lat QCD.RP QCD.Tide Lyre Grass Wilson Patria Patria.Depth Patria.Hub Patria.Exposure Lattice Cylinder
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
variable (a:Axis)
lemma folded (f g:Insertion n 6)(x:Grid n) : Action.adj a ⇑(f*g) x=Action.adj a g x*Action.adj a f x:=by simp only [eye_value,ContinuousMap.mul_apply,tilt_mul]
include hr
lemma pastV (f g: Insertion n 6)(h:⇑g=Action.adj a f): R.average g=star (R.average f):=by
    suffices hr' : R.raw g=star (R.raw f) by change (_:ℂ) *_ = star (R.Z⁻¹*R.raw f); rw[hr',star_mul,star_inv₀, R.Z_real, Complex.star_def, Complex.conj_ofReal,mul_comm]
    let V:= pull (K:=su.El) (Signed.mirror a) (0:Site n); let F(z:Gₙ):= b ((W*f) z); let Z(z:Gₙ):= star (F z)
    change joint _=star (joint _); unfold joint; have hp(z:Gₙ):b ((W*g) z)=Z (V z):=by
         rw [show (W*g) z= _ from (?_ : (W*g) z=Action.adj a ⇑(W*f) z)]; · rw [eye_value]; exact tilt_amp _ (eye_sq _) _
         rw [folded, eye_pivot _ _ hr,←h]; change W z*(g z)= g z* (W z); exact ((show Plus (W z) from by unfold Plus; rw [Regulator.density_apply,map_smul, show grade _=gauss (R.D z) from gauss_plus _]).central _).eq.symm
    simp_rw [hp]; have hz: Continuous Z:=by unfold Z F; fun_prop
    have hM:MeasurePreserving V μ μ:=prior_pull ..; rw [← integral_map hM.aemeasurable (hM.map_eq.symm ▸ (hz.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)).aestronglyMeasurable),hM.map_eq]; exact integral_conj
lemma strums (L:List I)(x y:I→ Insertion n 6)(h:∀ i∈L,Action.adj a ⇑(x i)=y i): R.average (L.reverse.map y).prod=star (R.average (L.map x).prod):=by
    apply pastV R hr a; funext z; induction L with
    | nil=>simp only[List.reverse_nil,List.map_nil,List.prod_nil]; unfold Action.adj; change (1:E)=changeVars _ (dagger (1:E)); rw [dagger_one,map_one]
    | cons j l ih=>
        simp only [List.map_cons,List.prod_cons,List.reverse_cons,List.map_append,List.prod_append,List.map_nil,List.prod_nil,mul_one, ContinuousMap.mul_apply,folded]; rw [h j (List.mem_cons_self ..), ih (fun i hi=>h i (List.mem_cons_of_mem _ hi))]
end MoveR
end YM.Massive.Tarn.Dispersed
#print axioms YM.Massive.Tarn.Dispersed.MoveR.strums
