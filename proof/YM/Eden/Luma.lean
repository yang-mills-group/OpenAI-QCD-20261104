import YM.Eden.Esme
import YM.Massive.Ribbon.Euph
/-! # covariance of FULL lattice normalization. at minor and major scales.A -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eden
open Function Lattice Laurent Bloch Metric RG Filter Arise Arise.Range
open Finset YM.Bank Precision Matrix
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open QCD QCD.Lat QCD.Free QCD.Flume QCD.Bank Next.Free
open QCD.Creek QCD.Anomaly QCD.Cove QCD.Kit QCD.Bloom QCD.Pine QCD.Grass
open Massive Massive.UV Patria Patria.Exposure Revolve TorusPCAC.Geometry TorusPCAC.Geometry.AxisB
variable {c:Side}{N k m:ℕ}{I:Type}[Fintype I]
open QCD.Cost
variable (F:Train k)(hk:2 ≤ k)(G:Spike)
lemma orbitS {X Y:Sheet c}(ha:X*Y=1)(U: Sheet c)(hb:U∈unitary _)(hx:aura U Y=Y): aura U X=X :=by
    rw[← Matrix.inv_eq_left_inv ha]; nth_rw 2 [← hx]; unfold aura; simp only [Matrix.mul_inv_rev]; have hu:U*star U=1:=hb.2; rw [(Matrix.inv_eq_left_inv hu),(Matrix.inv_eq_right_inv hu)]; simp only [Matrix.mul_assoc]
omit hk -- maybe not included
local notation "M"=> stage F c
local notation "Mo"=> unbarred F c
local notation "R"=> TorusPCAC.Jet.Cmat
variable (s: Signed) (o:Site c)
include hk
lemma rollingS (t:Site c→ℂ)(ht: Glare s 0 0 o t)(hp:Swing s G): aura (hues o s t G) M=M:=by
     let X:= hues o s t G; let P:Plan k:= (passport hk).some; apply orbitS (links_inv ..).1 _ (colour_wheel ht hp);
     rw [← bare_this P]; rw [← spin_wood ht hp]; have hh : pull s o (1:Grid c)=1:=by funext i; unfold pull Step.read; split <;> simp
     rw [hh]
lemma twist_board (u:su.El) : let X:= siteRot (fun _ : Site c=>u); aura X M=M:=by
     intro X; let P:Plan k:= (passport hk).some; apply orbitS (links_inv ..).1 X (siteRot_u ..);
     let h:=fun _ : Site c=>u; have he: Lattice.gauge h (1:Grid c)=1:=by funext i; simp [Lattice.gauge,h]
     rw[← bare_this P]; change siteRot h*_ *_= _; rw [← orbital, he]
local notation "X"=> onSpin c R
local notation "Y"=> onSpin c (R⁻¹)
lemma oppositeS : (Y * M * X).transpose=M:=by
     let P:Plan k:= (passport hk).some; have hh:TorusPCAC.Stencil.conjGrid (1: Grid c)=1:=funext (fun _=>map_one Reflection.dual);
     have hx: (Y*Mo*X).transpose=Mo:=by rw [← bare_this P]; nth_rw 1 [← hh]; exact unrolled ..
     have hz: Y*X=1:=fee; have hl:= links_inv F c; let V:=unbarred F c; nth_rw 2 [show M=V⁻¹ from stage_eq ..]; symm; apply Matrix.inv_eq_left_inv; change _*Mo = _; nth_rw 1 [← hx]; rw [← Matrix.transpose_mul]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc X Y _,mul_eq_one_comm.mp hz,one_mul,← Matrix.mul_assoc Mo M _,hl.2, one_mul,hz,Matrix.transpose_one]
lemma chiralS : Chiral (chirality c) M :=by
    let P:Plan k:=(passport hk).some; have hz: Chiral (chirality c) Mo:=by rw[← bare_this P]; exact spinO ..
    unfold Chiral; let X':=chirality c; rw [stage_eq]; have hL: X'⁻¹=X':=Matrix.inv_eq_left_inv (chi_sq); have ht : star Mo=X'*Mo*X':=hz; rw [show star (Mo⁻¹:Sheet c)=(star Mo)⁻¹ from ?_,ht]; · rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev,hL]; simp only [Matrix.mul_assoc]; rfl
    rw[Matrix.star_eq_conjTranspose,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_nonsing_inv]
lemma tilt_copy (u:Axis): eyeP c u * star (copies 6 M)*eyeP c u=copies 6 M:=by
    let s := Signed.mirror u; let Xv:= eyeP c u; let S :Sheet c:= stage F c; let G:= Jobs c 6 g5; let U:= copies 6 S
    have he:copies 6 (hues (0:Site c) s (prism s) (g5*gamma u))=Xv*G:=(orts u).symm
    have ht: Xv*G*U*star (Xv*G)=U:=by rw [← he, ← copies_star]; exact Eq.trans (show _= copies 6 (aura _ S) from (by unfold U aura; simp only [copies_mul])) (congr_arg _ (rollingS F hk _ s 0 (prism s) (smoke _) (Swing.mir u)))
    have hQ: star U= G* U*G:=by unfold U; rw [←copies_star]; change copies _ (star M)=_; rw [show star M= _ from (show Chiral (chirality c) (stage F c) from chiralS _ hk)]; unfold G; simp [Jobs,copies_mul]; rfl -- unfold M
    change Xv*star U*Xv=U; rw [hQ]; rw [star_mul,show star G=G from phase_star, show star Xv=Xv from eye_star _] at ht; simp only [mul_assoc] at *; exact ht
end YM.QCD.Eden
#print axioms YM.QCD.Eden.oppositeS
#print axioms YM.QCD.Eden.tilt_copy
