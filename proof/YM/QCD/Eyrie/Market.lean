import YM.QCD.Quarry.Vista

/-! # A local real jet (matrix code entries ordinary metric-free; interpreted
at any common precision), growing directions
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Finset
open Push.Uniform YM.Further.PhysicalPeriodLimitF933 Jacobi Withdrawal
open scoped Topology Matrix ContDiff BigOperators Classical
variable {X Y Z W : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable {n : Side} {I J K M: Type} [Fintype J] [Fintype K] [Fintype M]
lemma made {R: Type} [NormedRing R] [NormedAlgebra ℝ R] (v : X)
    {f g : X→R} {x : X} (h : ContDiffAt ℝ ω f x) (k : ContDiffAt ℝ ω g x) :
    blade v (fun x=> f x*g x) x=blade v f x*g x+f x*blade v g x := by
  unfold blade
  rw [fderiv_fun_mul' (h.differentiableAt (by simp)) (k.differentiableAt (by simp))]; exact add_comm ..
lemma blade_plus (v : X) {f g : X→Y} {x : X} (h : ContDiffAt ℝ ω f x) (k : ContDiffAt ℝ ω g x) :
    blade v (fun x=> f x+g x) x=blade v f x+blade v g x:=by unfold blade; rw [fderiv_fun_add (h.differentiableAt (by simp)) (k.differentiableAt (by simp))]; rfl
lemma blade_neg (v : X) {f:X→Y} {x:X} (h: ContDiffAt ℝ ω f x): blade v (fun x=> -f x) x= -blade v f x:=by unfold blade; rw [fderiv_fun_neg]; rfl
lemma blade_spear (v:X) {f:X→Y} {g:X→ℝ} {x:X} (h:ContDiffAt ℝ ω g x)(k:ContDiffAt ℝ ω f x):
    blade v (fun x=> g x • f x) x= blade v g x • f x+g x • blade v f x:=by
  unfold blade; rw [fderiv_fun_smul (h.differentiableAt (by simp)) (k.differentiableAt (by simp))]; exact add_comm .. 
lemma retell (v:X)(L : Y→L[ℝ] Z){f : X→Y}{x:X} (h:ContDiffAt ℝ ω f x) :
    blade v (L ∘ f) x=L (blade v f x):=by unfold blade; rw [fderiv_comp _ L.differentiableAt (h.differentiableAt (by simp)), L.fderiv]; rfl
lemma retold (v w:X)(L : Y→L[ℝ] Z){f : X→Y}{x:X} (h:ContDiffAt ℝ ω f x):
    Jacobi.mixed v w (L ∘ f) x=L (Jacobi.mixed v w f x):=by
  have he: blade w (L ∘ f)=ᶠ[𝓝 x] L ∘ blade w f:= (h.eventually (by simp)).mono fun _ he=>retell w L he
  apply Eq.trans _ (retell v L (smooth w h)); exact DFunLike.congr_fun he.fderiv_eq v
lemma transfuse (L:X→L[ℝ] Y) {x:X} (v:X) {f:Y→Z} (h:ContDiffAt ℝ ω f (L x)): blade v (f ∘ L) x=blade (L v) f (L x):=by
  unfold blade; rw [fderiv_comp x (h.differentiableAt (by simp)) L.differentiableAt, L.fderiv]; rfl
lemma adapt (L:X→L[ℝ]Y) (v w:X) {f:Y→Z}{x:X} (h:ContDiffAt ℝ ω f (L x)): Jacobi.mixed v w (f ∘ L) x=Jacobi.mixed (L v) (L w) f (L x):=by
  have hh : blade w (f ∘ L)=ᶠ[𝓝 x] blade (L w) f ∘ L:= (L.continuous.continuousAt.tendsto.eventually (h.eventually (by simp))).mono fun _ he=> transfuse L w he
  unfold Jacobi.mixed; exact Eq.trans (DFunLike.congr_fun hh.fderiv_eq v) (transfuse L v (smooth _ h))
lemma blade_same (v:X){f g:X→Y}{x:X} (h:f=ᶠ[𝓝 x] g): blade v f x=blade v g x:= DFunLike.congr_fun h.fderiv_eq v
lemma repeated (v w:X){f g:X→Y}{x:X} (h:f=ᶠ[𝓝 x] g): Jacobi.mixed v w f x=Jacobi.mixed v w g x:=blade_same v ((eventually_eventually_nhds.mpr h).mono fun _ hk=>blade_same w hk)
lemma rotate_area {R: Type} [NormedRing R] [NormedAlgebra ℝ R] (v w : X)
    {f g : X→R} {x : X} (h : ContDiffAt ℝ ω f x) (k : ContDiffAt ℝ ω g x) :
    Jacobi.mixed v w (fun x=> f x*g x) x=Jacobi.mixed v w f x*g x+blade w f x*blade v g x+(blade v f x*blade w g x+f x*Jacobi.mixed v w g x):=by
  have he:blade w (fun x=> f x*g x)=ᶠ[𝓝 x] fun x=> blade w f x*g x+f x*blade w g x:= ((h.eventually (by simp)).and (k.eventually (by simp))).mono fun _ ht=> made w ht.1 ht.2
  unfold Jacobi.mixed; rw [blade_same v he,blade_plus v ((smooth w h).mul k) (h.mul (smooth w k)), made v (smooth w h) k,made v h (smooth w k)]
lemma enroll (v w:X){f:I→X→Y}{s : Finset I} {x:X}(h : ∀ i∈s,ContDiffAt ℝ ω (f i) x): Jacobi.mixed v w (fun y=>∑ i∈s,f i y) x=∑ i∈s,Jacobi.mixed v w (f i) x:=by
  rw [iter _ _ (ContDiffAt.sum h), show (fun y=>∑ i∈s,f i y)=∑ i∈s,f i from funext fun i => (Finset.sum_apply ..).symm, iteratedFDeriv_sum_apply (fun i hi=> (h i hi).of_le le_top), _root_.sum_apply]; exact sum_congr rfl fun i hi=> (Jacobi.iter _ _ (h _ hi)).symm
lemma considers (v:X){f:X→Positions J}{g:Positions J→Y}{x:X} (h:ContDiffAt ℝ ω f x)(k:ContDiffAt ℝ ω g (f x)):
    blade v (g ∘ f) x=∑ i : J, Withdrawal.move v f x i • blade (Push.Uniform.bolt i) g (f x):=by
  unfold blade; rw [fderiv_comp _ (k.differentiableAt (by simp)) (h.differentiableAt (by simp)),ContinuousLinearMap.comp_apply, by_row]; simp_rw [Withdrawal.turn _ h]
lemma considered (v w : X) {f:X→Positions J}{g:Positions J→Y}{x:X} (h: ContDiffAt ℝ ω f x) (hg: ContDiffAt ℝ ω g (f x)):
    Jacobi.mixed v w (g ∘ f) x=(∑ i:J,rise v w f x i • blade (Push.Uniform.bolt i) g (f x)) + ∑ i:J, ∑ j:J, Withdrawal.move w f x i • Withdrawal.move v f x j • Jacobi.mixed (Push.Uniform.bolt j) (Push.Uniform.bolt i) g (f x):=by
  let M (x:X)(i:J) := Withdrawal.move w f x i; let N (x:Positions J)(i:J) := blade (Push.Uniform.bolt i) g x
  have he : blade w (g ∘ f)=ᶠ[𝓝 x] fun y=>∑ i:J,M y i • N (f y) i:= ((h.eventually (by simp)).and (h.continuousAt.tendsto.eventually (hg.eventually (by simp)))).mono fun _ ht=> considers w ht.1 ht.2
  have hh i : ContDiffAt ℝ ω (fun x:X=>M x i) x:= smooth w ((contDiffAt_pi.mp h) i)
  have hi i := smooth (Push.Uniform.bolt i) hg
  unfold Jacobi.mixed; rw [blade_same v he, series v (F:=fun i y=> M y i • N (f y) i) (fun i _=> (hh i).smul ((hi i).comp _ h)), ← sum_add_distrib]; refine sum_congr rfl fun i _=> ?_
  rw [blade_spear v (f:=fun x=> N (f x) i) (hh i) ((hi i).comp _ h),show blade v (fun x => N (f x) i) x=_ from considers v h (hi i), Finset.smul_sum]
end YM.QCD.Eyrie
