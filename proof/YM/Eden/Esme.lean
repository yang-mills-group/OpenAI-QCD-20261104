import YM.Eden.Stake
import YM.Patria.Reflect
import YM.QCD.Revolve.Reef
/-! # Actual unnormalized spin covariance, genuine transformations. -/
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
-- charge via all links deck.Twist produces on *X* ordinary star.transpose.
variable (P:Plan k)(F:Train k)(b:Site c)(U: Grid c)
local notation "CU"=> TorusPCAC.Stencil.conjGrid U
lemma turnsDeck (L:Cover→ℝ)(h: Summable fun i=>‖L i‖): deck b (CU) L= Twist (deck b U L):=by
     let Z:= LinearMap.toContinuousLinearMap ({ toFun:=Twist, map_add':=fun _ _=>by simp [Twist], map_smul':=fun c x=> by simp [Twist] } : Sheet c→ₗ[ℝ]Sheet c)
     unfold deck; rw[show Twist (∑' i, _)= Z (∑' i:Cover,(L i:ℂ) • mote b U i) from rfl, Z.map_tsum ((motes h b U).of_norm)]
     apply tsum_congr; intro i; change _=Twist ((L i:ℂ) • _);
     have hm:mote b (CU) i= Twist (mote b U i):=by unfold mote; simp_rw [twist_road U b]; simp only [Twist,transpose_sum, Matrix.conjTranspose_smul,Matrix.transpose_smul,Matrix.conjTranspose_sum,Complex.star_def,map_inv₀,map_natCast]
     rw [hm]; simp [Twist] -- map_tsum versions
local notation "R₀"=> onSpin c TorusPCAC.Jet.Cmat
local notation "R₁"=> onSpin c TorusPCAC.Jet.Cmat⁻¹
local notation "G"=> TorusPCAC.Jet.Cmat
-- find ns
lemma wall_real (i:Axis) : walls P b F (CU) i= Twist (walls P b F U i):=by
     let L:= P.Herm F i; unfold walls arcL; dsimp only; rw[turnsDeck _ _ L (Herm_valid P ..),twist_shift]
     have hx(i:Sheet c):Twist (1-i)=1-Twist i:=by simp[Twist]
     have ha(i j:Sheet c): Twist (half i j)=half (Twist i) (Twist j):=by simp[Twist,half]
     have hb(i:Sheet c): Twist (leaves i)=leaves (Twist i):=by unfold leaves; rw [Grass.twist_mul,Matrix.star_eq_conjTranspose i,Matrix.star_eq_conjTranspose, back_twist] -- latter maybe
     have hd(i j:Sheet c): Twist ((P.μ:ℂ) • i+j)=(P.μ:ℂ) • Twist i+ Twist j:=by simp[Twist]
     unfold L; rw [hd, ha, hb,hb,hb]; simp only [Grass.twist_mul, ← Matrix.star_eq_conjTranspose]; rw [show Twist (star (1-shift b U i))=star (Twist (1-shift b U i)) from back_twist _,hx]

lemma arc_commutes (i: Axis)(X:Spike): Commute (walls P b F U i) (onSpin c X) :=by
    let L:=onSpin c X; let A:=arcL b U i; let Z:=deck b U (P.Herm F i)
    have h(X:Spike) : Commute (arcL b U i) (onSpin c X):= Commute.sub_left (Commute.one_left _) (shift_spin ..)
    have hQ(X:Spike): Commute (star A) (onSpin c X):=by have he:=congr_arg star (h (star X)).eq; rw [star_mul,star_mul,on_spin_star,star_star] at he; exact he.symm
    have hz(X:Spike): Commute Z (onSpin c X):= sailor _ _ _ (Herm_valid P ..) _
    have hm(f:Sheet c)(h:∀ x:Spike,Commute f (onSpin c x)):Commute (leaves f) L:=by have he:=congr_arg star (h (star X)).eq; rw [star_mul,star_mul,on_spin_star,star_star] at he; exact Commute.mul_left he.symm (h X)
    exact Commute.add_left ((hm A h).smul_left _) ((Commute.add_left (hm (Z*A) (fun i=>(hz i).mul_left (h i))) (hm (Z*star A) (fun i=>(hz i).mul_left (hQ i)))).smul_left _)
lemma unbend (i:Axis) : (R₁ * walls P b F (CU) i * R₀).transpose=walls P b F U i:=by
     rw [Matrix.mul_assoc, (arc_commutes ..).eq,← Matrix.mul_assoc,fee,one_mul, wall_real,Twist,Matrix.transpose_transpose]; exact realwalls ..
lemma vein_real (i:Axis)(hj:2 ≤ k): (R₁ * vein b F i (CU)*R₀).transpose= -(star (vein b F i U)):=by
    let A:=deck b (CU) (alphaT F i); let D:=deck b U (alphaT F i); let X:=onSpin c (gamma i); have h:A*R₀=R₀*A:=sailor b _ _ (al_snap F i hj) _
    have hp:(R₁*X*R₀).transpose= -X:=by unfold X; rw [on_spin_mul,on_spin_mul, ←on_spin_trans, TorusPCAC.Jet.Selector.moves_C]; exact opposite _ -- namespace 
    change ((R₁*(X*A))*R₀).transpose= -star (X*D); rw [← Matrix.mul_assoc,Matrix.mul_assoc _ A,h,← Matrix.mul_assoc,Matrix.transpose_mul, hp,Matrix.mul_neg,star_mul, show star X=X from (by unfold X; rw [on_spin_star,gamma_star]),show Aᵀ = star D from (by rw [show A=Twist D from turnsDeck b U _ (al_snap F i hj), Twist,Matrix.transpose_transpose]; rfl)] -- likely
lemma unweave (i:Axis)(hj:2≤k): (R₁*skewL (vein b F i (CU))*R₀).transpose=skewL (vein b F i U):=by
    have he:= vein_real F b U i hj; have hx:=congr_arg star he
    have hR: star R₀=R₁:=by rw [on_spin_star, TorusPCAC.Jet.Selector.inverse_C, TorusPCAC.Jet.Cmat,star_mul,gamma_star,gamma_star]
    rw [← hR, show ∀ i:Sheet c,star (i.transpose)= (star i).transpose from fun _=>by ext; simp[Matrix.star_eq_conjTranspose],star_mul,star_mul,star_star, hR, ← Matrix.mul_assoc] at hx
    unfold skewL; rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.transpose_smul,Matrix.mul_sub,Matrix.sub_mul,Matrix.transpose_sub,he,hx,star_neg,star_star]; abel_nf
lemma unrolled (X:Plan k)(v:Train k) : (R₁*wood X b v (CU)*R₀).transpose=wood X b v U:=by unfold wood; rw [Finset.mul_sum,Finset.sum_mul,transpose_sum]; refine sum_congr rfl (fun i _=>?_); rw [mul_add,add_mul,Matrix.transpose_add, unbend,unweave _ _ _ _ X.good]
end YM.QCD.Eden
#print axioms YM.QCD.Eden.unrolled
