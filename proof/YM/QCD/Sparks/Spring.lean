import YM.QCD.Sparks.Soft

/-! # birth rule for curvature stencils, normalized by factorial -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary Push.Uniform Run
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume Work.F03 Revolve
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {n:Side}{p k:ℕ}{r B:ℝ}{I:Type}

lemma curl_read (x:Cnr n)(c:Cover)(j:PlaqAxes)(z: su.ColorIndex): bill (page x z) c (Lattice.square j.val.1 j.val.2) =faceCurl (wrap n c,j) (arm su n 1 x) z:=by
  unfold faceCurl; rw [← fundamental]
  generalize Lattice.square j.val.1 j.val.2=w
  induction w generalizing c with
  | nil=> rfl
  | cons a w ih=> rw [bill,linkSum,ih];
                     simp only [map_add,wrap_vec,PiLp.add_apply]; congr 1; rcases a with ⟨a,_|_⟩ <;> simp [page,Step.used]; all_goals rfl
lemma tint_smul (W:Rudder.Bloom k)(c:Fin k→su.Color)(t:ℝ): W.hues (fun i=> t • c i)=(t^k:ℝ) • W.hues c:=by
  unfold Rudder.Bloom.hues; rw [Finset.smul_sum]; apply sum_congr rfl; intro i _; simp_rw [PiLp.smul_apply, smul_eq_mul, prod_mul_distrib, prod_const, card_univ,Fintype.card_fin]; push_cast; rw [mul_smul]; rw [← Complex.ofReal_pow]; rfl
lemma portage (t: Site n)(U: Grid n)(w:Walk)(x:Site n): ‖Eyrie.winding x w t U‖ ≤ 1 := by
  have hg (x : Site n)(w:Walk): ‖shimmer t x w‖=1:=by
    induction w generalizing x with
    | nil=>exact norm_one
    | cons a w h=>rw [shimmer,norm_mul,h,mul_one]; unfold glint; cases seam_cases (n:=n) t (a.used x).1 (a.used x).2 <;> simp_all -- t rather than 0
  unfold Eyrie.winding; rw [norm_smul,hg,one_mul]; exact rotation_price (touch_u (x:=colour (travel U x w)) ⟨su.mat_star_mul _,su.mat_mul_star _⟩)
@[fun_prop] lemma winding_cont (i : Site n) (w:Walk)(t: Site n): Continuous (Eyrie.winding i w t):=by
  exact Continuous.const_smul (g:=fun U : Grid n=> TouchL (colour (travel U i w))) (TouchL.continuous.comp (colour_cont.comp (continuous_travel ..))) (shimmer t i w)
lemma rack (w:Walk) (t i:Site n): Eyrie.winding i w t 1=shimmer t i w • 1:=by unfold Eyrie.winding; rw [show travel (1:Grid n) i w=1 from ?_,show colour 1=1 from rfl,touch_one]; induction w generalizing i with
  | nil=>rfl
  | cons a w h=> rw [travel,h,mul_one]; cases hz:a.neg<;>simp [Step.read,hz]

def lepton (W : Bloom k)(x:Cnr n)(i : Site n):= W.hues fun j=>faceCurl (slotFace (W.petals j) i) (arm su n 1 x)
def vowel (W : Bloom k)(x:Cnr n)(i j: Row n) :ℂ:=entryR (t:=0) 1 W.tail (lepton W x) i j
lemma vok (W: Bloom k)(x:Cnr n)(i j:Row n): Tendsto (fun t:ℝ=> (t^k)⁻¹ • W.tonic 0 (input su n (t • x)) i j) cutRay (𝓝 (vowel W x i j)):=by
  have hh: Tendsto (fun t:ℝ=> input su n (t • x)) cutRay (𝓝 1):=by
    have hv: ContinuousAt (input su n) 0:= (Army.powL (v:=id) contDiffAt_id).cont
    have hx:Tendsto (fun t:ℝ=> t • x) cutRay (𝓝 0):=Stationary.along x
    rw [← input_zero]; exact hv.tendsto.comp hx
  have he (p : Site n): Tendsto (fun t:ℝ=> (t^k)⁻¹ • W.taste (input su n (t • x)) p) cutRay (𝓝 (lepton W x p)) := by
    have ht (t:ℝ) (p) : (t^k)⁻¹ • W.taste (input su n (t • x)) p=W.hues fun i=> t⁻¹ • (W.petals i).atSite (Precision.represent (t • arm su n 1 x)) p:=by unfold Bloom.taste; rw [tint_smul,inv_pow,input,map_smul]
    have H j:=slot_limit (W.petals j) p (arm su n 1 x)
    have hx := (tendsto_pi_nhds (f:=fun t:ℝ=>fun i=> t⁻¹ • (W.petals i).atSite (Precision.represent (t • arm su n 1 x)) p)).mpr H
    simp_rw [ht]; exact ((show Continuous W.hues from by unfold Bloom.hues; fun_prop).continuousAt.tendsto).comp hx
  unfold vowel; simp_rw [at_books,entryR]; split
  next hb =>
    have he' := (he i.1).mul ((winding_cont i.1 W.tail 0).continuousAt.tendsto.comp hh)
    let U (t:ℝ):= Eyrie.winding i.1 W.tail (0:Site n) (input su n (t • x)); let Y (t:ℝ):= W.taste (input su n (t • x)) i.1
    rw [show (fun t:ℝ=> (t^k)⁻¹ • (Y t* U t) i.2 j.2)=(fun t=> (((t^k)⁻¹ • Y t)*U t) i.2 j.2) from funext fun _=> by rw [Matrix.smul_mul]; rfl] -- defeq
    obtain ⟨L,H⟩:=ink_touch i.2 j.2; simp_rw [← H]; exact L.continuous.continuousAt.tendsto.comp he'
  simp only [smul_zero]; exact tendsto_const_nhds
-- termwise radial ok by uniform slots. Hess correspond all other orientations all forests.
end YM.QCD.Sparks
