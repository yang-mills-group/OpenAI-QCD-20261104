import YM.TorusPCAC.Geometry.Switch
import YM.TorusPCAC.Geometry.Charge
import YM.TorusPCAC.Jet.Conjugation

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
 # C and K5 laws at every field and with spectators
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Geometry.AxisB
open QCD QCD.Lat QCD.Kit QCD.Grass Lattice Wilson Finite Finset MeasureTheory Function Filter RG Revolve Ward Switch Jet.Selector Jet QCD.Flume
open scoped Matrix Topology BigOperators Kronecker Matrix.Norms.Frobenius Classical
variable {n c f : Side} (D:StepData c f) (V : Grid f)(U:Grid n)(t:Site n)(X Y:Spike) {N:ℕ}
lemma roll (z:ℂ): onSpin n (z • X)=z • onSpin n X:=by unfold onSpin wave; rw [Matrix.smul_kronecker, ride_smul]; rfl
lemma on_spin_sub : onSpin n (X-Y)=onSpin n X-onSpin n Y:=by rw [eq_sub_iff_add_eq,on_spin_add,sub_add_cancel]
lemma opposite : onSpin n (-X) = -onSpin n X:=by rw [← neg_one_smul ℂ, roll,neg_one_smul]
lemma on_spin_trans : onSpin n Xᵀ=(onSpin n X)ᵀ:=by
 have hh : wave Xᵀ=(wave X)ᵀ:=by unfold wave; ext i j : 1; by_cases he:i.2=j.2 <;> simp [Matrix.one_apply,he,Ne.symm]
 ext i j; by_cases hp : i.1=j.1 <;> simp [onSpin, rr, hh, hp,Ne.symm]

abbrev Jobs (n : Side) (N:ℕ) (X:Spike):= copies N (onSpin n X)
lemma pay (h : Y*X=1) : Jobs n N Y*Jobs n N X=1:=by simp only [Jobs,← copies_mul,on_spin_mul,h,on_spin_one,copies_one]
lemma shifted (z:Fields n N): Stencil.spinChange n X (-Y) z=shiftC (Jobs n N X) (Jobs n N Y) z:=by
 rw [shiftC,Stencil.spinChange,opposite,show copies N (-onSpin n Y)= -copies N (onSpin n Y) from (by ext ⟨i,u⟩ ⟨j,v⟩; by_cases he:u=v <;> simp [copies,Matrix.blockDiagonal_apply,he]),Matrix.transpose_neg]
lemma real_bare (B : Torus n N): Twist (B.fermion U) = ((Jobs n N g5)*(B.fermion U)*(Jobs n N g5))ᵀ:=by
 rw [Twist,← Matrix.star_eq_conjTranspose]; unfold Jobs
 unfold copies Torus.fermion; rw [block_star,← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul]; congr 2; ext1 i; exact Lat.gamma5 _ _ _
lemma fifth_real (B : Torus n N): Stencil.five _ (B.weight U)=B.weight U:=by
 let X : Matrix (Modes n N) (Modes n N) ℂ:= Jobs n N g5; have hx:X*X=1:=pay _ _ g5_sq; have hv:Xᵀ=X:=by unfold X Jobs copies; rw [Matrix.blockDiagonal_transpose]; simp only [← on_spin_trans,g5_trans]
 rw [B.weight_complex,map_smulₛₗ]; simp only [Complex.conj_ofReal]; congr 1
 unfold Stencil.five; dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]; rw [cc_gauss, g5_trans, shifted, gauss,map_weight,tune,real_bare]
 change NormedSpace.exp (form (X*(X*_ *X)ᵀ*X)ᵀ) = _; simp only [Matrix.transpose_mul, hv, Matrix.transpose_transpose,mul_assoc, hx,mul_one]; rfl

lemma twist_shift (i:Axis) : shift t (Stencil.conjGrid U) i=Twist (shift t U i):=by
 ext a b; have hb (z): thread t (Stencil.conjGrid U) i z=Twist (thread t U i z):=by
    ext k l; change seam t z i * star (colour (U (z,i)) k l) = star (seam t z i * colour (U (z,i)) k l); rw [star_mul,seam_real,mul_comm]
 have hh (z:Mat): touch (Twist z)=Twist (touch z):=by ext k l; by_cases h : k.1=l.1 <;> simp [touch,Twist,Matrix.one_apply,h]
 simp only [shift,rr,hb,hh,Twist,Matrix.transpose_apply,Matrix.conjTranspose_apply]; split <;> simp [*]
lemma back_twist {A B:Type*}(D : Matrix A B ℂ): Twist Dᴴ=(Twist D)ᴴ:=by ext; simp
lemma twist_road (w:Walk): routeM t (Stencil.conjGrid U) w=Twist (routeM t U w) :=by
 induction w with
 | nil=> simp [routeM,Twist]
 | cons a l ih=>
    rw [show routeM _ (Stencil.conjGrid U) (a::l)=Kit.leg t (Stencil.conjGrid U) a * routeM t (Stencil.conjGrid U) l from rfl, ih, show routeM t U (a::l)=Kit.leg t U a*routeM t U l from rfl, twist_mul, Kit.leg, Kit.leg, twist_shift]; congr 1; split; exact (back_twist _).symm; rfl
lemma compass_lo (i : Axis) : (Cmat⁻¹*lo i*Cmat)ᵀ=hi i:=by
 simp only [lo,hi,mul_sub,sub_mul,mul_one,pays_C,smul_mul_assoc,mul_smul_comm,Matrix.transpose_smul,Matrix.transpose_sub, moves_C,Matrix.transpose_one,sub_neg_eq_add]
lemma compass_hi (i:Axis) : (Cmat⁻¹*hi i*Cmat)ᵀ=lo i:=by
 rw [show hi i=1-lo i by rw [eq_sub_iff_add_eq, add_comm,Lat.projectors],mul_sub,sub_mul,mul_one,pays_C,Matrix.transpose_sub,Matrix.transpose_one, compass_lo]; rw [← Lat.projectors i,add_sub_cancel_right]
local notation "L"=>onSpin n Cmat
local notation "R"=>onSpin n Cmat⁻¹
lemma fee : R*L=1:=by rw [on_spin_mul, pays_C,on_spin_one]
lemma compass_step (i : Axis) : (R*singleHop t (Stencil.conjGrid U) i*L)ᵀ =singleHop t U i:=by
 have hp (W : Sheet n) (X : Spike)(h : Commute W L): (R*(onSpin n X * W)*L)ᵀ = Wᵀ * onSpin n (Cmat⁻¹ * X * Cmat)ᵀ:=by
    rw [← mul_assoc R _,mul_assoc _ W L,h.eq,← mul_assoc, on_spin_mul,on_spin_mul,Matrix.transpose_mul,on_spin_trans]
 rw [singleHop,singleHop,mul_add,add_mul, Matrix.transpose_add,hp _ _ (shift_spin ..),hp _ _ (back_spin ..),twist_shift,compass_lo,compass_hi, show (star (Twist (shift t U i)))ᵀ= _ from twist_turn _,Twist,Matrix.transpose_transpose, ← Matrix.star_eq_conjTranspose,(shift_spin ..).eq,(back_spin ..).eq, add_comm]
lemma compass_bare (m:ℝ) : (R*bareD t (Stencil.conjGrid U) m*L)ᵀ=bareD t U m:=by
 unfold bareD; simp_rw [mul_add,add_mul, Finset.mul_sum,Finset.sum_mul,mul_sub,sub_mul,mul_one,fee,mul_smul_comm,smul_mul_assoc]; rw [Matrix.transpose_add, Matrix.transpose_sum]; simp only [Matrix.transpose_smul, Matrix.transpose_sub, compass_step,Matrix.transpose_one]; rw [mul_one,fee,Matrix.transpose_one] -- order
lemma compass (B:Torus n N): Stencil.charge _ (B.weight (Stencil.conjGrid U))=B.weight U:=by
 have hB : ((Jobs n N Cmat⁻¹)*(B.fermion (Stencil.conjGrid U))* Jobs n N Cmat)ᵀ=B.fermion U:=by unfold Jobs copies Torus.fermion; rw [← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul,Matrix.blockDiagonal_transpose]; congr 1; ext1 i; exact compass_bare ..
 rw [B.weight_complex, Reflection.energy_alt, map_smul,B.weight_complex,Stencil.charge,shifted,gauss,map_weight,tune,hB]; rfl
local notation "J"=>meanSpin (N:=N) D V
local notation "s"=>prototype D.patch
local notation "g"=>sliceL s D.sizes
lemma model : meanSpin (N:=N) D (Stencil.conjGrid V)=Twist J:=by
 have hv : scoop g=Twist (scoop g):=by ext i j; by_cases he: mouth g i=j <;> simp [scoop,he]
 have hh : tied s D.sizes 0 (Stencil.conjGrid V)= Twist (tied s D.sizes 0 V):=by
    unfold tied lineF; simp_rw [twist_road]; simp only [Twist,Matrix.conjTranspose_smul,Matrix.conjTranspose_sum,Matrix.transpose_smul,Matrix.transpose_sum,Matrix.conjTranspose_mul,Matrix.transpose_mul]; simp only [Complex.star_def, Complex.conj_ofReal, map_inv₀,map_natCast]; unfold Twist at hv; rw [← hv]
 unfold meanSpin; rw [hh]; ext i j; by_cases h : i.2=j.2 <;> simp [Twist,Matrix.blockDiagonal_apply,h,Ne.symm]
lemma free_slots : J*Jobs f N X=Jobs c N X*J:=by
 have h : scoop g * onSpin f X=onSpin c X*scoop g:=roots ..
 have hv (l:Walk) : scoop g*routeM 0 V l*onSpin f X=onSpin c X*(scoop g*routeM 0 V l):=by rw [Matrix.mul_assoc,(spinM ..).eq, ← Matrix.mul_assoc, h,Matrix.mul_assoc]
 have he : tied s D.sizes 0 V*onSpin f X=onSpin c X*tied s D.sizes 0 V:=by unfold tied lineF; simp only [Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul,hv]
 unfold meanSpin Jobs copies; rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]; congr 1; ext1; exact he
lemma drum {k:Side} : (Jobs k N X)ᴴ=Jobs k N (star X):=by rw [← Matrix.star_eq_conjTranspose,Jobs,← copies_star,on_spin_star]
lemma bound_to : Jᴴ * Jobs c N X=Jobs f N X* Jᴴ:=by
 have hx:= congrArg Matrix.conjTranspose (free_slots (N:=N) D V (star X)); simp_rw [Matrix.conjTranspose_mul,drum,star_star] at hx; exact hx.symm
lemma transpJob {k:Side}: (Jobs k N X)ᵀ=Jobs k N Xᵀ:=by simp only [Jobs,copies,Matrix.blockDiagonal_transpose,← on_spin_trans]
lemma tick : Twist (Jobs n N X) = Jobs n N (Twist X):=by rw [Twist,drum,transpJob]; rfl
lemma whole_join (b:ℝ)(h : Y*X=1):
    ((whole (Jobs f N Y) (Jobs c N Y))*joinD b (Twist J) 0*(whole (Jobs f N X) (Jobs c N X)))ᵀ=joinD b J 0:=by
 let F (k:Side):= Jobs k N X; let G (k:Side):= Jobs k N Y
 let Q:= Twist J
 have hU k:G k*F k=1:=pay X Y h
 have ha : Q*F f=F c * Q:= by
    have h:= congrArg Twist (free_slots (N:=N) D V (Twist X)); rw [twist_mul,twist_mul,tick,tick,twist_turn] at h; exact h
 have hb : Qᴴ*F c= F f*Qᴴ:=by
    have he:= congrArg Twist (bound_to (N:=N) D V (Twist X)); rw [twist_mul,twist_mul,tick,tick,twist_turn, back_twist] at he; exact he
 change (whole (G f) (G c)*joinD b Q 0*whole (F f) (F c))ᵀ= _
 have hh : G f*Qᴴ*F c=Qᴴ:=by rw [Matrix.mul_assoc,hb,← Matrix.mul_assoc, hU,Matrix.one_mul]
 have hc : G c*Q*F f=Q:=by rw [Matrix.mul_assoc,ha,← Matrix.mul_assoc,hU,Matrix.one_mul]
 simp only [whole,joinD,zero_add, Matrix.fromBlocks_multiply,Matrix.zero_mul, Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul, add_zero, smul_zero,mul_one,hU,Matrix.fromBlocks_transpose,hc,hh,Matrix.transpose_smul,Matrix.transpose_one, show Qᵀ=Jᴴ from Matrix.transpose_transpose _, show Qᴴᵀ=J from twist_turn _]
 rw [← Matrix.mul_assoc (G f) Qᴴ,Matrix.mul_assoc _ Q (F f),ha, ← Matrix.mul_assoc,hh, Matrix.transpose_mul]; rw [show Qᵀ=Jᴴ from Matrix.transpose_transpose _, show Qᴴᵀ=J from twist_turn _]
lemma step_fifth (F:Density f N) : Stencil.five c (TorusPCAC.high D F V)=TorusPCAC.high D (fun U=>Stencil.five f (F U)) V:=by
 unfold Stencil.five TorusPCAC.high; dsimp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply]; rw [sheath_real,g5_trans, shifted,shifted]; exact sheath_spins _ _ _ _ (pay _ _ g5_sq) (pay _ _ g5_sq) 1 J _ (whole_join _ V _ _ _ g5_sq) _
lemma step_charge (F:Density f N): Stencil.charge c (TorusPCAC.high D F (Stencil.conjGrid V))=TorusPCAC.high D (fun U=>Stencil.charge f (F (Stencil.conjGrid U))) V:=by
 unfold TorusPCAC.high Stencil.charge; dsimp only; rw [model,shifted,shifted]; exact sheath_spins _ _ _ _ (pay _ _ pays_C) (pay _ _ pays_C) 1 J _ (whole_join _ V _ _ _ pays_C) _
end YM.TorusPCAC.Geometry.AxisB

#print axioms YM.TorusPCAC.Geometry.AxisB.compass
#print axioms YM.TorusPCAC.Geometry.AxisB.compass_bare
