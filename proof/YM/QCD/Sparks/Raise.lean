import YM.QCD.Sparks.Swell

/-! # actual issue at a width relative to supplied curvature-debts
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary Run
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume Work.F03 Revolve RG Tavern
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {S:SparkMesh}{r a C:ℝ}{p k:ℕ}{F:S.Field}{K:Typewriter k}
lemma foundation (h:Clan S F){m:ℕ→ℕ}(hk:k≤2) (hb:Exhibit S F k r C m K) (hc:0 ≤ C)(he:0<r)(hv:∀ n,EmptyThrough (F n) k) (hp:Fractal (rivet K) a (req k a C))(ha:0<a) (x:Cnr (S.n p))(y:Site (S.n p)):
    Run.cell (surge (metastage (rivet K) _) (fun _:Fin k=>x)) 0 y=Run.cell (surge (F p) (fun _:Fin k=>x)) 0 y:=by
  let n:= S.n p
  rw [(sculpt hp ha _).2 x, lyrical S h hb hc he _ y hv hk]; change Run.cell _ 0 _=∑' i,frameR i K x y
  let f (i:Snug k):= epilogue (rivet K i) x
  have hi:= bough hp x|>.of_norm
  let L:Sheet n→L[ℝ] Bundle:=LinearMap.toContinuousLinearMap { toFun:=fun z=>(k.factorial:ℝ) • Run.cell z 0 y, map_add':=fun a b=> by rw [cell_add,smul_add],map_smul':=fun i a=> by ext z w; exact (smul_comm (k.factorial:ℝ) i (Run.cell a 0 y z w)) }
  have he : HasSum (fun i: Snug k=>frameX i.1 i.2 K x y) (L (∑' i,f i)):= L.hasSum hi.hasSum
  change L (∑' i,f i)=_; rw [← he.tsum_eq, he.summable.tsum_sigma]
  simp_rw [tsum_fintype,groupR]
  let W':= (flyer k).symm
  rw [← W'.tsum_eq]
  have hg := (W'.summable_iff (f:=fun i=>frameR i K x y)).mpr (plain_pay K hb.ceiling hc ‹0<r› x y|>.of_norm)
  erw [hg.tsum_prod]; apply tsum_congr; intro i; rw [tsum_fintype]; rfl
lemma solace {J L : S.Field}(hq: ∀ i, ContDiffAt ℝ ω (J i) 0)(he:∀ i, EmptyThrough (J i) k)(h:∀ i,ContDiffAt ℝ ω (L i) 0)(hx:∀ i,EmptyThrough (L i) k) :
    ∀ i, EmptyThrough (J i-L i) k :=by
  intro i m hm; rw [iteratedFDeriv_sub_apply (hq i|>.of_le le_top) (h i|>.of_le le_top),he i m hm,hx i m hm,sub_zero]
lemma levy (h:Clan S F){m:ℕ→ℕ}(hk:k≤2)(hb:Exhibit S F k r C m K) (hc:0≤C)(he:0<r)(hv:∀ n,EmptyThrough (F n) k)(hp:Fractal (rivet K) a (req k a C))(ha:0<a)(j : ℕ):
    EmptyThrough (F j-metastage (rivet K) _) (k+1) := by
  let n:=S.n j
  let B i:= metastage (rivet K) (S.n i); let T:=F j-B j
  have H :=(h.way j).less (quota hp ha)
  refine fun i hi=>?_ ; rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with ht|ht
  · exact solace (J:=F) (L:=B) (fun i=> (h.way i).ready) hv (fun i=> (quota hp ha).ready) (fun i=> (sculpt hp ha _).1) j i ht
  subst i
  refine Tensor.ext_diag _ _ (H.ready.iteratedFDeriv_comp_perm) (fun _ _=>rfl) (funext fun x=>?_)
  change surge T (fun _:Fin k=>x)=0
  refine acrossTown H x k (fun x y=> ?_); unfold surge; rw [iteratedFDeriv_sub_apply (h.way j|>.ready.of_le le_top) (quota hp ha|>.ready.of_le le_top), _root_.sub_apply]
  have hg := foundation h hk hb hc he hv hp ha (p:=j) x y; ext a w; change (surge (k:=k) (F j) _) _ _ - (surge (k:=k) (B j) _) _ _=0; exact sub_eq_zero.mpr (Matrix.ext_iff.mpr hg.symm a w)

-- chain period crossing priced birth off any clan. matching cost uniform independent input fields
open Metric Set Push.Uniform in
lemma lanterns (k:ℕ)(hv:k≤2)(r C:ℝ)(hr:0<r)(hC:0≤C) : ∃ a W, 0 < a∧0 ≤ W ∧ ∀ (S:SparkMesh)(F:S.Field), (∀ i, glyph (traceG _) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (F i) r C)→∃ m P, Exhibit S F k a W m P := by
  obtain ⟨P,hp,H⟩:= float_norm
  let a:=r/4; let W:=P*C
  refine ⟨a,W,div_pos hr (by norm_num),mul_nonneg hp hC,fun S F h=>?_⟩
  have H (i:ℕ) (p:Tilt k): ‖design (F i) p‖≤ W*aim a p:=pitch_sum _ hp H p hr hC (h i) hv
  let U (p:Tilt k):Set Bundle:= closedBall 0 (W*aim a p)
  have he : IsCompact ((Set.univ : Set (Tilt k)).pi U):= isCompact_univ_pi fun i => isCompact_closedBall ..
  have hz : ∀ i:ℕ,(design (F i))∈(Set.univ : Set (Tilt k)).pi U := fun i p _=>mem_closedBall_zero_iff.mpr (H i p)
  obtain ⟨K,hk,m,hm,h⟩:= he.isSeqCompact hz
  exact ⟨m,K,hm,H,(tendsto_pi_nhds.mp h),fun p=> mem_closedBall_zero_iff.mp (hk p (Set.mem_univ p))⟩

lemma issue (k:ℕ)(hk:k≤2)(hr:0<r)(hc:0≤C) : ∃ a W, 0 < a ∧ 0 ≤ W ∧∀ (S:SparkMesh)(F:S.Field), Clan S F→(∀ i, glyph (traceG _) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (F i) r C)→ (∀ n,EmptyThrough (F n) k) →
      ∃ P : Snug k → Bloom k,Fractal P a W ∧ ∀ n, EmptyThrough (F n-metastage P _) (k+1) :=by
  obtain ⟨w,A,hw,h,H⟩:=lanterns k hk r C hr hc
  let a:=w/4; have ha:0<a:=div_pos hw (by norm_num)
  refine ⟨a,req k a A,ha,req_pos h ha k,fun S F hi he Hx=>?_⟩
  obtain ⟨m,P,HP⟩:= H S F he
  have hp : Fractal (rivet P) a (req k a A):=standout HP.ceiling (lim_color HP hi.way) (by unfold a; linarith) h ha
  exact ⟨_,hp,levy hi hk HP h hw Hx hp ha⟩
end YM.QCD.Sparks
