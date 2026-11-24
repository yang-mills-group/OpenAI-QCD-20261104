import YM.Hypnos.Berries
import YM.UVNext.PRICED_KERNELS.Gaps
/-! # Shortened Wick step data.Can.On precisely scalar curvatures. Cost in output distances. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hypnos
open Filter Function Lattice Wilson Tree RG Pressure Finset MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations Push.SectorMeasure Push.SectorMeasure.Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Coat Blaze.Vine
open Shell Channel

open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Next.SectorChange
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Malachite PhysicalNext.JointLoad.Heir
open Matrix Census Green Mask Pulse Itinerary Matter Poll Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{β τ C μ W:ℝ} {o: ConnectedActivityE6.Target.Order G W}{Q:ConnectedActivityE6.Target G P} {X:S.Choices} {r u t d A M D:ℝ}{F:Tree.Forest S.ratio}{n:ℕ}
open Current
-- work on full color native lift
namespace Fruit
open UVNext.PricedKernels FreeResolvent
variable {ι κ:Type}{r t :ℕ}{n m:Side}{σ α η ε:ℝ}
lemma tensorAnnuity (G:Gauge)(X:Matrix (Body r c) (Body t f) ℝ)(e: Site c→Site n)(d':Site f→Site n)
    (h: (native n).Rows (e∘Prod.fst) (d'∘Prod.fst) α M X) : (native n).Rows (e ∘ Prod.fst) (d' ∘ Prod.fst) α M (FreeResolvent.tensor G X):=by
   constructor; rintro ⟨y,a,b⟩; convert h.bound (y,a); rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro j _; simp only [tensor,Matrix.of_apply]; simp [apply_ite abs,mul_ite]
lemma downl [Fintype κ] (e: ι→Site f)(g:κ→Site f)(r:Ratio c f){X:Matrix ι κ ℝ}(hp:0≤α) (h: (native f).Rows e g α M X): (native c).Rows (r.parent ∘ e) (r.parent∘g) α (Real.exp α*M) X:=by
   constructor; intro i; refine le_trans ?_ (mul_le_mul_of_nonneg_left (h.bound i) (Real.exp_pos _).le); rw [Finset.mul_sum]; refine sum_le_sum fun j _ =>?_ ; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
   unfold Cost.weight; rw [← Real.exp_add]; have hp': ((separation (r.parent (e i)) (r.parent (g j))):ℝ) ≤ separation (e i) (g j)+ (1:ℝ):= by exact_mod_cast YM.Work.E04.parent_separation r (e i) (g j)
   exact Real.exp_monotone (show _≤ _ from (mul_le_mul_of_nonneg_left hp' hp).trans_eq (by simp only [native]; ring))
variable (G S)
local notation "points'"=> S.ratio.parent ∘ Prod.fst
local notation "b'"=> (S.patch.L.val:ℝ)
variable {H:Bed}{B:Bed}{p p':Clip}{T₀:Towers S.patch.L}
def pla_cost (t M L:ℝ):=
   let h:ℝ:=Fintype.card (TypeFace 2); Real.exp (t/L)*((h*M)*(Real.exp t*(h*(M/L^2)))*(h*M))
lemma upl (hf:H.dual_diag.strip α M)(hg:B.diagonal.strip α M)(hp:T₀.T.strip α (M/b'^2))(he:0 ≤ M)(ht:0<α) :
    (native c).Rows (points') Prod.fst (α/b') (pla_cost α M b') (view G S H B T₀):=by
     let Y :ℝ:= Fintype.card (TypeFace 2); let L:= (S.patch.L.val:ℝ); let K:=S.ratio; have hL : 1≤ L:=Nat.one_le_cast.mpr S.patch.L.property
     let t:= α/L; have h:0<t:=by unfold t; positivity
     have hc := Annuity.cut (Annuity.paid_site hf ht.le f) (div_le_self ht.le hL) le_rfl
     have hv:= Annuity.paid_parent (S.ratio) hg ht.le; have hw:= Annuity.paid_cross (g:=S.ratio) hp ht.le
     let a:= K.embed; let Y':= (Y*M)*(Real.exp α*(Y*(M/L^2)))*(Y*M)
     have hy:= ((hc.times hw h.le (show 0≤Real.exp α*(Y*(M/L^2)) by unfold Y; positivity)).times hv h.le (show 0≤ Y*M by unfold Y; positivity)); have hx: (native f).Rows Prod.fst (a ∘ Prod.fst) t Y' (view G S H B T₀):= tensorAnnuity _ _ (fun i=>i) a ⟨hy⟩
     have he:=downl _ _ K h.le hx; convert he; funext i; exact (K.embed_parent i.1).symm; exact rfl

lemma curveP (L:Side)(α:ℝ) (hp:0<α) :∃ Y M₀ :ℝ,0≤Y ∧ 0≤M₀ ∧∀ (c f:Side)(S:StepData c f)(F:Tree.Forest S.ratio),
    S.patch.L=L → (native c).Rows (S.ratio.parent∘Prod.fst) (theta S.ratio F) α Y (plane S F (G:=G)) ∧
     (native c).Rows (theta S.ratio F) (S.ratio.parent∘Prod.fst) α M₀ (plane S F (G:=G)).transpose:=by
    obtain ⟨X,h,H⟩:=Next.Free.delta_budget 1 α
    let Y:ℝ:=Fintype.card (TypeFace 1) * X; let Z:ℝ:= Fintype.card (TypeFace (1+1))*X
    refine ⟨Real.exp α*Y,Real.exp α*Z,(by unfold Y; positivity),(by unfold Z; positivity),fun c f S F _=>?_⟩
    have hh:= tensorAnnuity G _ id id (downgrade (physical_rows H hp.le f) hp.le); have hv:= tensorAnnuity G _ id id (downgrade (physical_cols H hp.le f) hp.le); let A:=(tensor G (Exterior.d 1 f)); have hx : plane S F=A.submatrix id (plant F):=by ext i j; unfold plane; unfold FreeResolvent.insertion; simp [Matrix.mul_apply,mul_ite,eq_comm]; rfl
    have hA: (native f).Rows Prod.fst Prod.fst α Y A:=hh; have hB : (native f).Rows Prod.fst Prod.fst α Z A.transpose:=by unfold A; rw [tensor_transpose]; exact hv
    rw [hx,Matrix.transpose_submatrix]; exact ⟨(downl _ _ S.ratio hp.le hA).submatrix id (plant_inj F),(downl _ _ S.ratio hp.le hB).submatrix (plant F) Function.injective_id⟩
lemma floats {K:KernelChoices}(J:Patch)(v s M:ℝ)(hv:0<v)(hs:0<s)(hM:0≤M):∃ u C:ℝ,0<u∧0 ≤ C∧∀ (c f:Side)(S:StepData c f)(F:Tree.Forest S.ratio)(H:Bed)(B:Bed)(p p':Clip)(T₀:Towers S.patch.L),S.patch=J→S.kernel=K→ Larger (G:=G) S→ H.metric.strip s M → Floor H p f v M → Floor B p' c v M → Towers.Diagonal S H B T₀→
    (native c).Rows (S.ratio.parent ∘ Prod.fst) (S.ratio.parent ∘ Prod.fst) u C (curtain G S H B T₀):=by
    let O:= billing G J K.penalty s M; let η:= treeFare G J K v; have ht : 0 ≤ O:=billing_nn _ _ _ _ _ hM; have hν : 0<η := treeFare_pos _ _ _ hv
    let R:=safeRate s O η; let r:=R/2; have hR:0 < R:= rate_pos hs ht hν; have he:=half_pos hR; let V:=torusPay (Co J.L (PAC G 1)) (R-r)
    obtain ⟨Y,M₀,hY,hX,hP⟩:= curveP G J.L r he
    refine ⟨r,max 0 ((Y*(V*(η/2)⁻¹))*M₀),he,le_max_left ..,?_⟩
    intro c f S F H B p p' T₀ hp hK hL hhW hF hv' hm
    obtain ⟨h1,h2⟩:= hP c f S F (hp ▸ rfl); let A:=treeMatrix G S F H.metric
    have h: (native c).Schur (theta S.ratio F) (theta S.ratio F) s O A:=by have h:=treeSchur (G:=G) S F hs.le hM hhW; rw [hp,hK] at h; exact h
    have hg: Gap A η:=by have hg:=tree_gap (G:=G) S F H.metric hL hv (Gap.mk (fun v => (hF.uniform.1 v).1)); rw [hp,hK] at hg; exact hg
    have hW: (native c).Volume (theta S.ratio F (G:=G)) (R-r) V:=by have hv:=treeVolume (G:=G) S F (s:=R-r) (sub_pos.mpr (half_lt_self hR)); rw [hp] at hv; exact hv
    have hz:= (FreeResolvent.resolve_schur ht hs h hg hν (show (0:ℝ)≤0 from le_rfl) hW).rows; simp only [FreeResolvent.resolve,zero_smul,add_zero] at hz
    have hV:0≤ V:= by unfold V; exact le_trans (sum_nonneg fun i _=> ( (native c).weight_nn _ _ _)) (hW.bound 0)
    have hd:= ((h1.mul hz he.le (mul_nonneg hV (by positivity))).mul h2 he.le hX).mono le_rfl (le_max_right 0 _)
    exact Eq.subst (motive:=fun W: Matrix (FreeResolvent.Slot G f (1+1)) (FreeResolvent.Slot G f (1+1)) ℝ=>(native c).Rows (S.ratio.parent ∘ Prod.fst) (S.ratio.parent ∘ Prod.fst) r _ W) (factorKl (S:=S) H B T₀ hm G F hL hF hv' hv hv).symm hd
end Fruit
end YM.Hypnos
#print axioms YM.Hypnos.Fruit.upl
#print axioms YM.Hypnos.Fruit.floats
