import YM.QCD.Cedar.Ribbon

/-!
# All-field covariant extension of the free Wilson trajectory, global gap source

Positive bulk uses pos/neg covariant shifts separately. Not just a small field estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pine
open Lat Cost Lattice Wilson Function Finset Flume
open Laurent Bloch YM.Next.Free Metric Kit Free
open scoped Matrix.Norms.L2Operator Topology BigOperators Matrix
variable {n : Side} {j : ℕ} (P : Plan j) (t : Site n)

/-- letter uses the oriented transporter. -/
def vein (v : Train j) (a : Axis) (U : Grid n) := onSpin n (gamma a) * deck t U (alphaT v a)

def leaves (V : Sheet n):= star V*V
def half (X Y : Sheet n) := ((2:ℂ)⁻¹) • (X+Y)
def arcL (U : Grid n) (a : Axis):=1-shift t U a
def walls (v : Train j) (U : Grid n) (a : Axis) :=
  let Z := arcL t U a; let F := deck t U (P.Herm v a)
  (P.μ:ℂ) • leaves Z + half (leaves (F*Z)) (leaves (F*star Z))
def skewL (Y : Sheet n) := ((2:ℂ)⁻¹) • (Y-star Y)
def wood (v : Train j) (U : Grid n) := ∑ a : Axis,(walls P t v U a + skewL (vein t v a U))

lemma realwalls (v : Train j) (U : Grid n) (a : Axis): star (walls P t v U a) = walls P t v U a:=by simp only [walls,half,leaves,star_add,star_mul,star_star,star_smul]; simp
lemma skewed (Y : Sheet n):star (skewL Y)=-skewL Y :=by unfold skewL; rw [star_smul,star_sub,star_star,← neg_sub,smul_neg]; simp
lemma unital (v : Train j) (U : Grid n) (a : Axis) (x : Vec (Row n)) : P.μ*‖diff t U a x‖^2 ≤ Cost.form (walls P t v U a + skewL (vein t v a U)) x:= by -- inspect binder
  have hz : Cost.form (skewL (vein t v a U)) x=0:=by
    have he:= star_form (skewL (vein t v a U)) x; rw [skewed, show Cost.form (-(skewL _)) _ = _ from (by simp [Cost.form]: Cost.form (-(skewL (vein t v a U))) x= -Cost.form (skewL (vein t v a U)) x)] at he; linarith
  change P.μ*_ ≤ Cost.form _ x
  unfold walls half leaves; rw [add_form,hz,add_zero,add_form, real_form,show ((2:ℂ)⁻¹)=(((2:ℝ)⁻¹):ℂ) by norm_num, ← Complex.ofReal_inv,real_form,add_form]; simp only [Cost.square]; unfold diff; exact le_add_of_nonneg_right (by positivity)
lemma engrave (v : Train j) (U : Grid n) (x : Vec (Row n)) : P.μ * estate t U x ^2 ≤ Cost.form (wood P t v U) x:=by
  have he (s : Finset Axis):P.μ * ∑ i∈s,‖diff t U i x‖^2 ≤ Cost.form (∑ i ∈s,(walls P t v U i+skewL (vein t v i U))) x:= by
    induction s using Finset.induction_on with
    | empty=> simp [Cost.form]
    | insert i s hi ih=> rw [sum_insert hi,sum_insert hi,add_form,mul_add]; exact add_le_add (unital P t v U i x) ih
  rw [estate,Real.sq_sqrt (by positivity)]; exact he _
lemma lawful (U : Grid n) (a : Axis): leaves (star (arcL t U a))= leaves (arcL t U a):=by
  unfold leaves arcL; have he:= shift_u t U a; rw [star_star,star_sub,star_one]; simp [mul_sub,sub_mul,he.1,he.2]; abel

lemma Herm_valid (v : Train j) (a) : Summable fun x=> ‖P.Herm v a x‖:=by obtain ⟨σ,C,hp,hc,H⟩:= P.herm_paid (fun _ : Unit=>v) fun _=>a; exact ((H ()).unweighted hp.le).2.1
lemma al_snap (v : Train j) (a) (hj : 2≤j): Summable fun x=>‖alphaT v a x‖:=by obtain ⟨σ,C,hp,hc,H⟩:=alpha_cash hj (fun _ : Unit=>v); exact ((H a ()).unweighted hp.le).2.1
lemma orbit1 (k : Frame n) : siteRot k * 1 *star (siteRot k) = 1:=by rw [mul_one]; exact (siteRot_u k).2
lemma composed1 (k : Frame n) (A B : Sheet n): siteRot k*A*star (siteRot k)*(siteRot k*B*star (siteRot k))=siteRot k*(A*B)*star (siteRot k):=by
  simp only [mul_assoc]; rw [← mul_assoc (star _) (siteRot k), (siteRot_u _).1,one_mul]
lemma orbital (v : Train j) (U : Grid n) (k : Frame n): wood P t v (gauge k U)=siteRot k*wood P t v U*star (siteRot k):=by
  have hh (i): arcL t (gauge k U) i=siteRot k*arcL t U i*star (siteRot k):=by simp only [arcL,site_transform,mul_sub,sub_mul,mul_one,(siteRot_u k).2]
  have hs (i): vein t v i (gauge k U)=siteRot k*vein t v i U*star (siteRot k):=by rw [vein,motive _ _ _ _ (al_snap _ _ P.good),spinless]; rfl
  have hx (X:Sheet n):star (siteRot k * X * star (siteRot k))= siteRot k * star X * star (siteRot k):=by simp [mul_assoc]
  unfold wood; rw [Finset.mul_sum, Finset.sum_mul]; refine sum_congr rfl fun i _=>?_
  rw [hs, walls]; simp only [walls,hh,skewL, hx,half,leaves,motive _ _ _ _ (Herm_valid P v i),composed1, Matrix.mul_smul,Matrix.smul_mul,mul_sub,sub_mul,mul_add,add_mul]
lemma halo (X : Sheet n) (h : X*chirality n=chirality n*X) : star X * chirality n= chirality n * star X:= by have he:=congr_arg star h; simpa using he.symm
lemma spinO (v : Train j) (U : Grid n) : Chiral (chirality n) (wood P t v U):=by
  let J:=chirality n
  have hh (i : Axis):Commute (arcL t U i) J:= Commute.sub_left (Commute.one_left _) (shift_spin ..)
  have hw (i : Axis): Commute (deck t U (P.Herm v i)) J := sailor t _ _ (Herm_valid P ..) _
  have hm (X : Sheet n) (h : Commute X J):Commute (leaves X) J:= Commute.mul_left (show Commute (star X) J from halo X h) h
  have hb (i : Axis) : Commute (walls P t v U i) J:=by
    apply (hm _ (hh i)).smul_left _ |>.add_left; unfold half
    apply Commute.smul_left; apply Commute.add_left (hm _ ((hw i).mul_left (hh i))); exact hm _ ((hw i).mul_left (halo _ (hh i))) -- check
  have hz (i) : star (walls P t v U i)=J*walls P t v U i*J:=by rw [realwalls,← (hb i).eq, mul_assoc, chi_sq,mul_one]
  have hK (i) : J*vein t v i U*J= -vein t v i U:=by
    let F:=onSpin n (gamma i); let D:=deck t U (alphaT v i)
    have he : D*J=J*D:= sailor _ _ _ (al_snap v i P.good) _
    have hx : J*F= -(F*J):= by
      unfold J chirality F; rw [on_spin_mul,on_spin_mul]; -- check gamma
      rw [five,← add_eq_zero_iff_eq_neg,on_spin_add,add_neg_cancel,on_spin_zero]
    change J*(F*D)*J= _; rw [mul_assoc J (F*D) J,mul_assoc F D J,he,← mul_assoc F J,← mul_assoc J (F*J),← mul_assoc J F,hx,neg_mul,mul_assoc F,chi_sq,mul_one]; simp; rfl
  unfold Chiral wood; simp_rw [star_sum, Finset.mul_sum, Finset.sum_mul]; refine sum_congr rfl fun i _=>?_
  have hX := congr_arg star (hK i); rw [star_mul,star_mul, show star J=J from chi_star, star_neg, ← mul_assoc] at hX
  rw [star_add,hz,skewed,mul_add,add_mul]
  simp only [skewL,Matrix.mul_smul,Matrix.smul_mul,mul_sub,sub_mul]
  rw [hK,hX]; unfold J; simp only [smul_sub,smul_neg]; abel
@[fun_prop] lemma verdant (v : Train j):Continuous (wood P t v):=by
  unfold wood; refine continuous_finsetSum _ fun i _=>?_
  have hu := persist _ t (Herm_valid P v i); have hm:= persist _ t (al_snap v i P.good)
  unfold walls skewL vein half leaves arcL; fun_prop
end YM.QCD.Pine
