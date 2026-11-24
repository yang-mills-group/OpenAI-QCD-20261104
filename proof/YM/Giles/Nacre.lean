import YM.Gall.Civets
import YM.Giles.Magus
/-! Economical Allowance. Shift.C finite position (U matrix proofs) stable under totals and scales. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s σ :ℝ}{c:Side}{n l d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Complex (exp I)
noncomputable abbrev peaks (p:Flavor 6)(i j: Lat.Fiber)(X:G★) :ℝ:=∑ u:Site c,∑ v:Site c, sepW 0 u v^2* ‖uncoat X ((u,i),p) ((v,j),p)‖
-- for sums cost with respect to *local* readings supports.Д. holds for ANY sector. W degree pairs only. Includes scaling.
lemma p_plus (p:Flavor 6)(i j:Fiber)(X Y:G★): peaks p i j (X+Y)≤ peaks p i j X+peaks p i j Y:=by
    unfold peaks; rw [←sum_add_distrib]; refine sum_le_sum fun x _=>?_ ; rw [←sum_add_distrib]; refine sum_le_sum fun y _=>?_ ; rw[map_add,Matrix.add_apply,← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le ..) (sq_nonneg _)
lemma p_scaled(p:Flavor 6)(i j:Fiber)(X:G★)(s:ℂ): peaks p i j (s • X)=‖s‖*peaks p i j X:=by
     unfold peaks; simp_rw [map_smul, Finset.mul_sum,Matrix.smul_apply,norm_smul]; exact Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=> mul_left_comm ..
lemma peaks_g (p:Flavor 6)(i j:Fiber)(X:G★):0 ≤ peaks p i j X:= by apply sum_nonneg; intro j _; apply sum_nonneg; intro l _; exact mul_nonneg (sq_nonneg _) (norm_nonneg _)
variable (U:BudgetPoint)(g:su.Color)(F Y:Grid c→ Lat.Fields c 6)
structure Allow (n:ℕ)(a:ℝ):Prop where
   alive:Chart n F 1
   heatL: forall p i j, peaks p i j (F 1)≤ a
   fire:∀ (v: Cray c), U.dirBound 0 (ink g v)→∀ p i j, peaks p i j (tent g F v)≤ a
lemma allowance (h:Tutor 0 U F σ n m C)(hv:0 < σ)(hn:2 ≤ n)(hm: 2 < m)(he:1 ≤ U.order): Allow U g F U.order (C/σ^2):=by
    exact ⟨h.smooth, fun p i j=>fruitful h hv p p i j [] (by simp) (by simp) hn hm, fun v hi p i j=>by rw[determines g _ _ h.smooth he]; exact fruitful h hv p p i j _ he (List.forall_mem_singleton.mpr hi) hn hm⟩
lemma firesS (h:Allow U g F n a)(hf:Allow U g Y n t)(hn:1 ≤ n): Allow U g (F+Y) n (a+t):=by
    refine ⟨h.alive.add hf.alive,fun p i j=> (p_plus _ _ _ _ _).trans (add_le_add (h.heatL ..) (hf.heatL ..)),fun x hx p i j=>?_⟩; have H:tent g (F+Y) x=tent g F x+tent g Y x:=by rw [determines g _ _ (show Chart n (F+Y) 1 from h.alive.add hf.alive) hn,determines g _ _ h.alive hn,determines g _ _ hf.alive hn]; exact Push.Local.left_add _ h.alive hf.alive hn
    rw[H]; exact (p_plus ..).trans (add_le_add (h.fire _ hx ..) (hf.fire _ hx ..)) -- dot syntax hx .. maybe valid
lemma firesM (h:Allow U g F n a)(s:ℂ)(hn:1 ≤ n): Allow U g (s • F) n (‖s‖*a):=by
    let L:G★→L[ℝ]G★:= s • ContinuousLinearMap.id ℝ G★; have hx: s • F=L ∘ F:= rfl; have hf:Chart n (s • F) 1:=by rw [hx]; exact L.contDiff.contDiffAt.comp _ h.alive
    refine ⟨hf,fun p i j=>?_,fun x hv p i j=>?_⟩
    · rw [Pi.smul_apply,p_scaled]; exact mul_le_mul_of_nonneg_left (h.heatL ..) (norm_nonneg _)
    have hk:tent g (s • F) x= s • tent g F x:=by rw [determines g _ x hf hn,hx,left_linear L [ink g x] h.alive (show List.length _ ≤ _ from hn), determines g _ x h.alive hn]; rfl
    rw [hk,p_scaled]; exact mul_le_mul_of_nonneg_left (h.fire _ hv ..) (norm_nonneg _)
lemma poster (x:Cover)(h:Nearby x)(i j:Fiber)(p:Flavor 6) (Z:G★): peaks p i j (slidesD x Z) ≤4*peaks p i j Z:=by
     obtain ⟨k,hk⟩:=h; unfold peaks; rw [Finset.mul_sum]; let t:=wrap c x; let V:=Equiv.addRight t; rw[←Equiv.sum_comp V]; apply sum_le_sum; intro u _; rw[←Equiv.sum_comp V, Finset.mul_sum]; apply sum_le_sum; intro v _; let W(u v:Site c)(Z:G★):= uncoat Z ((u,i),p) ((v,j),p); change sepW 0 (u+t) (v+t)^2* ‖W (u+t) (v+t) (slidesD x Z)‖ ≤ 4*(sepW 0 u v^2 * ‖W u v Z‖); have he:W (u+t) (v+t) (slidesD x Z)=(heat x u*heat x v)*W u v Z:=congr_fun (congr_fun (thug (a:=p) (b:=p) (fun _=>Z) u v x) i) j
     rw[he,norm_mul,show ‖heat x u * heat x v‖=1 from (by rcases (glares x|>.sign u) with h|h <;> rcases (glares x|>.sign v) with he|he <;> simp [h,he]),one_mul,←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
     let M:= sepW 0 u v; have hv(x:Site c): pdist (x+t)≤ pdist x+1:=(pdist_triangle x t).trans (Nat.add_le_add_left ((flipT _ _ hk).1) _) -- dot notation length
     have hu : sepW 0 (u+t) (v+t) ≤ 2*M:=by
          rw [sep0]; unfold M; rw [sep0]; have he (x:Site c): (pdist (x+t):ℝ) ≤ pdist x+1:=by exact_mod_cast hv x
          suffices ht: max (pdist (u+t):ℝ) (pdist (v+t):ℝ) ≤ 1 + max (pdist u:ℝ) (pdist v:ℝ) by linarith[show 0 ≤ max (pdist u:ℝ) (pdist v:ℝ) from (by positivity)]
          rw[add_max]; apply max_le_max ((he u).trans (add_comm ..|>.le)) ((he v).trans_eq (add_comm ..)) -- parentheses
     exact (pow_le_pow_left₀ (zero_le_one.trans (arm ..)) hu 2).trans_eq (by rw[mul_pow]; unfold M; ring)
lemma shifting(t:Y★)(h:U.dirBound 0 (ink g t))(x:Cover)(hp:Nearby x): U.dirBound 0 (ink g ((2^U.power:ℝ)⁻¹ • floats x t)):=by
    intro i; let y:= i.1+wrap c x; rw [map_smul,Pi.smul_apply,norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_le_iff₀ (by positivity)]; change ‖ink g t (y,i.2)‖≤ _; apply (h ..).trans
    simp only[separation,sub_zero,Prod.fst]; rw[mul_left_comm ((2:ℝ)^_)]; apply mul_le_mul_of_nonneg_left (fancy i.1 _ _) U.threshold_pos.le
    obtain ⟨k,h⟩:=hp; exact (flipT x k h).1
lemma mart (h:Allow U g F n a)(hn:1 ≤ n)(x:Cover)(ht:Nearby x): Allow U g (march x F) n (4*(2:ℝ)^U.power*a):=by
     have ha: 0≤a:= (peaks_g 0 (0,0) (0,0) (F 1)).trans (h.heatL ..); refine ⟨marchC _ _ h.alive,fun p i j=>?_,fun v hv p i j=>?_⟩
     · rw [show march x F 1= slidesD x (F 1) from (by unfold march post; rw[pull_one]; rfl)]
       exact (poster x ht ..).trans ((mul_le_mul_of_nonneg_left (h.heatL ..) (by norm_num : (0:ℝ)≤4)).trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by norm_num) (one_le_pow₀ (by norm_num))) ha))
     rw [turnedK F x g _ h.alive hn]; apply (poster x ht ..).trans; let C:ℝ:=2^U.power; let q:=(C⁻¹ • floats x v); have H:= h.fire q (shifting U g v hv x ht) p i j; let L:= tent g F; rw [show tent g F (floats x v)=C • L q from (by rw[← map_smul]; unfold q; rw[smul_inv_smul₀ (by unfold C; positivity)]),show C • L q=(C:ℂ) • L q from (Complex.coe_smul ..).symm,p_scaled,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ C by unfold C; positivity)]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left H (by unfold C; positivity)) (show (0:ℝ)≤4 from by norm_num)).trans_eq (mul_assoc ..).symm
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.mart
#print axioms YM.Massive.Patria.Gall.allowance
