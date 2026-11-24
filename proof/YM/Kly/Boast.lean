import YM.Kly.Hurd
set_option autoImplicit false
set_option maxHeartbeats 610000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis
open OS (Cross)
open Fields (pointMoment distinct)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder
open MassiveTwoEstimates Spinor Spinor.Lift
variable {F:Fields} {S:F.Kernel}{V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){X:Bases F}{M':Momentum F}(U:X.Content C M')
local notation "a"=> timeAxis
variable (ha:∀ x:F.W,F.adj a (F.parity x)=F.parity (F.adj a x))
include P H Y R E ha
lemma tooth (y:P.algebra)(h:y.val V.omega0=0): y=0:=by
     apply Subtype.ext; apply DFunLike.coe_injective; apply (full P H).equalizer y.val.continuous continuous_const; funext v; change (y*v).val V.omega0=0; rw[possible P H Y R (E.reflected _) E.folded ha]; change v.val (y.val V.omega0)=0; rw[h,map_zero]
include U
lemma honorP (p:Pack F)(b:EuPin)(hb:b.IsRotation) : M₀ P (orbit R b p)=M₀ P p:=by
     let G:Subgroup EuPin:={
           carrier:={b|∀ x:Pack F,M₀ P (orbit R b x)=M₀ P x}
           one_mem':=fun x=>by rw [orbit1]
           mul_mem':=by intro x y hx hy i; rw [← oreM]; exact (hx _).trans (hy _)
           inv_mem':=by intro x hx i; apply Eq.trans (Eq.symm (show _ from hx (orbit R x⁻¹ i))); rw [oreM,mul_inv_cancel,orbit1] }
     have h:b∈G:=by
           refine prop_inherit G (fun i r x=>?_) b hb; apply sub_eq_zero.mp; apply tooth P H Y R E ha; change budG _ _-budG _ _=0; exact sub_eq_zero.mpr (encore P H Y R E U i r x)
     exact (show ∀ x:Pack F,_ from h) p
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.honorP
