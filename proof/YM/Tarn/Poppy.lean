import YM.Tarn.Alex
/-! Charge orientations and spin central character. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open Function QCD QCD.Lat Wilson Patria Patria.Depth Patria.Hub Lattice Cylinder Dispersed Fir YM.Fir UV Filter Set TensorProduct
open Poised Poised.Plans Poised.Plans.Stamp QCD.Grass
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius TensorProduct
variable {C:Sequence} {P:Calibration C} {n:ℕ} {Q:Choir}
namespace Pollens
variable (T: Pollens P Q) (hQ:Q.Domestic) (a:Axis)
include hQ
lemma even : Involutive T.parity:=by
    intro x; obtain ⟨d,x,rfl⟩:=hQ.tidal x none; rw [T.p,T.p]; exact congr_arg _ (Patria.Depth.chi_twice P.sym x)
lemma realL: Involutive T.charge:=by
    intro x; obtain ⟨d,x,rfl⟩:=hQ.tidal x none; rw [T.c,T.c]; apply congr_arg; apply Subtype.ext; rw [P.sym.chargeActs,P.sym.chargeActs]; exact UV.inv_c _
lemma reflex: Involutive (T.adj a):=by intro x; obtain ⟨d,x,rfl⟩:=hQ.tidal x none; rw [T.a,T.a]; apply congr_arg; apply Subtype.ext; rw [RawSym.adjActs,RawSym.adjActs]; exact UV.eyeTwist a _
lemma spurs : T.spin 1=1:=by
    ext1 u; obtain ⟨d,x,rfl⟩:=hQ.tidal u none; rw[T.w 1 1 (show EuPin.Lifts 1 1 from (map_one Signed.inclusionO).symm)]; rw [show P.sym.pin d 1 x=x from Subtype.ext (Eq.trans (RawSym.pinActs ..) (UV.pin_one _))]; rfl
lemma spine (p q:EuPin) (s t:Signed)(hp:p.Lifts s)(hq:q.Lifts t): T.spin (p*q)=T.spin p*T.spin q:=by
    ext1 u; obtain ⟨d,x,rfl⟩:=hQ.tidal u none; change T.spin (p*q) _=T.spin p (T.spin q _); rw [T.w _ _ (EuPin.life_mul hp hq),T.w q t hq,T.w p s hp]; change Q.focus none _ _=Q.focus none _ _; apply congr_arg; apply Subtype.ext; rw [RawSym.pinActs,RawSym.pinActs,RawSym.pinActs]; exact (UV.beam_pin ..).symm
omit hQ in
private lemma foe(d:ℕ)(u:FlavorTorus)(x:Pol d): UV.flavorAct u (UV.adj a x)=UV.adj a (UV.flavorAct u x):=by
    induction x using TensorProduct.induction_on with
    | zero=> simp
    | add x y hx hy=> simp [map_add,hx,hy]
    | tmul x y=>
         unfold UV.adj UV.flavorAct; simp_rw [TensorProduct.map_tmul]; apply congr_arg₂ (tmul ℂ); rfl
         let X(g: FlavorTorus):= UV.byFlavor g (fun i:SpinMode d=> i.2); let M:= UV.eyeW d a; let F:=Matrix.fromBlocks (X u) 0 0 (X u⁻¹); change changeVars F (changeVars M (dagger y))=changeVars M (dagger (changeVars F y)); rw [dagger_change,multipleChange,multipleChange]
         have he(g:FlavorTorus)(P:Spike): X g*flipTable a P = flipTable a P*X g:= run_coil g _ _ _ fun i j h=>by simp [flipTable,spinTable,h]
         rw [show M*F=Mstar F*M from ?_]; unfold F M UV.eyeW; rw[mstar_diag, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]; have hh(t:FlavorTorus):Mstar (X t)= X t⁻¹:= phase_conj ..; simp only [hh,_root_.inv_inv,Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,he]
lemma activeF (u:FlavorTorus):Function.Commute (T.flavor u) (T.adj a):=by -- Function.Commute? change
    intro x; obtain ⟨d,x,rfl⟩:= hQ.tidal x none; change T.flavor u (T.adj a _)=_; rw [T.a,T.f,T.f,T.a]; apply congr_arg; apply Subtype.ext; rw [RawSym.flavorActs,RawSym.adjActs,RawSym.adjActs,RawSym.flavorActs]; exact foe a d u _
end Pollens
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Pollens.spine
#print axioms YM.Massive.Tarn.Pollens.realL
#print axioms YM.Massive.Tarn.Pollens.activeF
