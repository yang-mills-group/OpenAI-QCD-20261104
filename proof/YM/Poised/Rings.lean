import YM.Poised.Summum
import YM.Poised.Doves
/-!
 # Actual output coordinates can truncate only log directions in their comparison; wind-preserving frame expense for rotated anchor per weighted slot.
 Proof uses power weighted spins separation, so all at all root charges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Chute
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource Cruising MultiNext.SignedSource.Lyre
variable {K: KernelChoices}(P:Flight j k)(h:l.val=c.val*P.L.val)(T:Tube su (Flight.visit P K h)) (R:BudgetPoint)
variable {X:Support l}{Y:Support c}{b b':Cover} {u v L:ℕ} {τ t vo A C M:ℝ}
open Kites Fountain MassiveQCD.Plate Costs Display Next.Foundations PhysicalNext.Repeat
local notation "F'"=>Lat.Fields c 6
lemma march_bound (c:Side)(o v:Site c)(i: Faces (Site c))(k:ℕ): Heir.spine k (locationP i) v ≤ (1+(separation o v:ℝ))^k *Heir.spine k (locationP i) o:=by
   unfold Heir.spine; rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity); have hp: (separation (locationP i) v:ℝ) ≤ separation (locationP i) o+(separation o v:ℝ):=by exact_mod_cast separation_triangle _ o v
   nlinarith [Nat.cast_nonneg (α:=ℝ) (separation o v),Nat.cast_nonneg (α:=ℝ) (separation (locationP i) o)]
-- prices.Max-view to paid spin.All cohorts.
lemma march_view (c:Side)(o v:Site c)(X:Lat.Fields c 6)(k:ℕ)(x:ℝ)(hx:0<x): MassiveQCD.Plate.view v k X x≤ (1+(separation o v:ℝ))^k*‖framesF (purseX o k x) X‖:=by
   let S:=(1+(separation o v:ℝ))^k; let f:= purseX o k x; have hS:1≤ S:=one_le_pow₀ (by simp)
   change ∑ j: Finset (Keys c 6),_ ≤ S*Creek.load f X; rw [dry f (purse_pos o k x hx), Finset.mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); have he j:f j=x*(1+(Stew.lens o j:ℝ))^k:= rfl; unfold MassiveQCD.Plate.toll; simp_rw [he]; rw [prod_mul_distrib,prod_const,mul_comm _ (x^i.card), mul_left_comm S]; apply mul_le_mul_of_nonneg_left _ (by positivity); by_cases hh:i=∅; · simp only [hh, sup_empty, bot_eq_zero,Nat.cast_zero,add_zero,one_pow,prod_empty,mul_one]; change 1≤ S*∏ j∈(∅:Finset (Keys c 6)), (1+(Stew.lens o j:ℝ))^k; simp [hS]
   obtain ⟨u,hu,h⟩:= Finset.exists_mem_eq_sup _ (Finset.nonempty_iff_ne_empty.mpr hh) (Stew.lens v); rw [h, ← Finset.mul_prod_erase _ _ hu]; apply (march_bound _ o v u k).trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Heir.spine_pos ..).le (one_le_prod (fun i _=>one_le_pow₀ (by simp)))) (zero_le_one.trans hS))
-- diag curvatureW original extension without needing full Χ curved. probes J. 
lemma curvatureD (d n:ℕ)(J:Labels.Jet su)(hn:n≤d):∃ C:ℝ,0≤C ∧ ∀ (l:Side)(Y:Grid l→Lat.Fields l 6)(b:Cover)(H:TaperHol)(R:BudgetPoint)(v a:ℝ),0≤a→ d*d ≤ R.power →let T:= stageZ (d:=d) H l b v ∘ Y; ContDiffAt ℝ d (T∘increment 1) 0 → (∀ i≤d,∀ α:Directions su l,R.dirBound (wrap l b) α → ‖leftDerivs T (List.replicate i α) 1‖ ≤ a) → ‖iteratedDeriv n (engine v (ZBand d)∘Beacon.moment H b (R.threshold • J) Y) 0‖ ≤ C*a:=by
    -- uniform comparision for each
    choose C hp h using fun (r:Fin (n+1))(q:OrderedFinpartition r.val)(j:Fin q.length)=> tau_cost d (q.partSize j) J ((q.partSize_le j).trans ((Nat.le_of_lt_succ r.isLt).trans hn))
    choose V hV hT using fun (r:Fin (n+1))(q:OrderedFinpartition r.val)=> mixed_budget (SpinPol d) su q.length (C r q) (hp r q)
    let W(r:Fin (n+1)):=∑ i: OrderedFinpartition r.val,V r i; let M:=∑ i: Fin (n+1),W i; have hm i:0≤ W i:= Finset.sum_nonneg fun j _=>hV i j; have hM:0 ≤ M:= sum_nonneg fun i _=>hm i; obtain ⟨A,hA,hE⟩:= Sieve.boost d n
    refine ⟨A*M,mul_nonneg hA hM,?_⟩; intro l Y b H R v a ha hμ T hh hδ;  let J':=R.threshold • J; let F:= producing (d:=d) H l b Y v J'; let L:= lode d J' l b H; have hL : F =ᶠ[𝓝 0] (T ∘increment 1) ∘ L:=by filter_upwards [stays J' d (1:Grid l) H b] with t ht; exact congr_arg T ht
    rw [show engine v (ZBand d) ∘ Beacon.moment H b (R.threshold • J) Y=(fun i=>endor i (F i)) from funext fun i=> (Sieve.stage_count ..).symm]; have hg : ContDiffAt ℝ d L 0:= lode_smooth J' d H l b; have hu:L 0=0:=inPlace ..; have hi: ContDiffAt ℝ d (T ∘ increment 1) (L 0):= hu.symm ▸ hh; have he : ContDiffAt ℝ d F 0:= ContDiffAt.congr_of_eventuallyEq (hi.comp _ hg) hL
    rw [mul_assoc]; apply hE (he.of_le (Nat.cast_le.mpr hn)) (M*a) (mul_nonneg hM ha); intro i hI; let p:Fin (n+1):=⟨i,Nat.lt_succ_of_le hI⟩; rw [hL.iteratedDeriv_eq, iteratedDeriv_vcomp_eq_sum_orderedFinpartition hi hg (Nat.cast_le.mpr (hI.trans hn)),hu]; apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right (single_le_sum (f:=W) (fun i _=>hm i) (mem_univ p)) ha)
    unfold W; rw [sum_mul]; refine sum_le_sum fun j _=>?_ ; have he:j.length ≤ d:= j.length_le.trans (hI.trans hn); refine hT p j R l 1 (wrap l b) T a (hh.of_le (Nat.cast_le.mpr he)) ⟨ha,hδ _ he⟩ _ ?_
    intro k s; exact (h p j k H l b R.threshold R.threshold_pos.le R.threshold_le s).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp) hμ) (mul_nonneg (hp p j k) R.threshold_pos.le))
-- Rescale & chart localization.Up front all stacks.
open Brim
lemma boundsQ (o v:Site c)(hi:separation o v ≤ k)(α:Directions su c) (K:BudgetPoint)(h:K.dirBound v α) : K.dirBound o (((1+(k:ℝ))^K.power)⁻¹ • Mom.screen Y α):=by
   let L:=(1+(k:ℝ))^K.power; have hp:0<L:=by unfold L; positivity
   intro e; change ‖L⁻¹ • (Mom.screen Y α e)‖≤ _; rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hp).le]; rw [inv_mul_le_iff₀ hp,Mom.screen_at]; split
   next _=>
      apply (h e).trans; rw [mul_left_comm]; let z:=separation e.1 o; refine mul_le_mul_of_nonneg_left ?_ K.threshold_pos.le; unfold L; rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity); have he : (separation e.1 v:ℝ)≤ (z:ℝ)+ k:=by exact_mod_cast (separation_triangle e.1 o v).trans (Nat.add_le_add_left hi z)
      nlinarith [Nat.cast_nonneg (α:=ℝ) z,Nat.cast_nonneg (α:=ℝ) k]
   next _=> rw [norm_zero]; exact mul_nonneg hp.le (mul_nonneg K.threshold_pos.le (by positivity))
-- charts-only upgrade handles x,y difference. works all.Table
lemma shiftD (F:Grid c→F')(K:BudgetPoint)(o v:Site c)(x:ℝ)(L:Side)(W:ℝ)(hx:0≤W)(he:ContDiffAt ℝ d (F∘increment 1) 0)(h:∀ i≤d, ∀ α:Directions su c,K.dirBound o α→‖α‖≤canopyW su L K.power x → ‖leftDerivs F (List.replicate i α) 1‖≤ W)(hp:coverNumber (radiusB x) Y≤ radiusB x)(ht:separation o v ≤ k)(hK:K.threshold ≤ 2*fiery su x L) (hY:o∈Y) (α:Directions su c)(hα:K.dirBound v α)(hn:n≤d): ‖leftDerivs (F∘splitF Y) (List.replicate n α) 1‖≤ ((1+(k:ℝ))^K.power)^d*W:=by
   let f:= F ∘ increment 1; let A:= (1+(k:ℝ))^K.power; have hA:1 ≤ A:=one_le_pow₀ (by simp); let β:= Mom.screen Y α; let γ:= A⁻¹ • β; have hγ : A • γ=β:=smul_inv_smul₀ (by linarith) β
   have hQ := boundsQ (Y:=Y) o v ht α K hα
   have hg:= pacing γ Y (fun i h'=>by unfold γ β; change A⁻¹ • (Mom.screen Y α i) = _; rw [Mom.screen_at,if_neg (by unfold Mom.needed; tauto),smul_zero]) K hY rfl hQ x L hp hK
   have hx:=h _ hn γ hQ hg
   have hm(X:Directions su c) : Tensor.diagonal (iteratedFDeriv ℝ n f 0) X=leftDerivs F (List.replicate n X) 1:=by
      rw [← iteratedDeriv_on_line (show ContDiffAt ℝ n f 0 from he.of_le (Nat.cast_le.mpr hn))]; have h0:= Fountain.diagnosis X F n; exact h0.symm
   rw [show leftDerivs (F∘splitF Y) (List.replicate n α) 1=leftDerivs F (List.replicate n β) 1 from ?_, ← hm β, ← hγ,Tensor.homogeneous,norm_smul,Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans hA) _), hm]
   · exact (mul_le_mul_of_nonneg_left hx (by positivity)).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hn) (by linarith))
   rw [Fountain.diagnosis α,Fountain.diagnosis β]; apply congr_arg (fun f => iteratedFDeriv ℝ n f 0 (fun _=>1)); funext t; change F (splitF Y (increment 1 (t • α)))=F _; rw [split_inc,map_smul];rfl
end Chute
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Chute.curvatureD
