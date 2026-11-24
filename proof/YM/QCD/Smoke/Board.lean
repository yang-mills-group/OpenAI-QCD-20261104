import YM.QCD.Smoke.Bill

/-! # Limit-anchor two-leg tensor, uncolored constraints. still local. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary Push.Uniform Run Tree RG
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume Sparks Jacobi
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {n N: Side} {r C:ℝ}{M:Cnr n→ ℝ}
abbrev Kite := Fin 2→Nub
def exposed (k:Kite): Tilt 2:=(0,k)
def flown (k:Kite)(r:ℝ):=aim r (exposed k)
lemma home_run (h:0<r): Summable fun p:Kite=>(1+(timbre (exposed p):ℝ))^2*flown p r:= (beam_use 2 h).comp_injective (i:=exposed) fun i j hi=>congr_arg Prod.snd hi
def chartB (k:Kite): Fin 2→Road n:=fun j=> (wrap n (k j).1,(k j).2)
def scene (M:Cnr n→ℝ)(p:Kite):ℝ:= if AtMap n (exposed p) then Push.Uniform.entry M 0 (chartB p) else 0
lemma scene_fit (h: Cigar M r C) (p:Kite) : ‖scene M p‖≤ C*flown p (r/4):=by
  unfold scene; split
  next he=>
    rw [Sparks.standing] at he; let v:= chartB (n:=n) p; have hx : Push.Uniform.entry M 0 v=Jacobi.mixed (Push.Uniform.bolt (v 0)) (Push.Uniform.bolt (v 1)) M 0:=by unfold entry; rw [iter _ _ h.W.host,show (fun i=> Push.Uniform.bolt (v i))=![_,_] from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)]; rfl -- check
    rw [show chartB (n:=n) p=v from rfl,hx]; apply (h.W.wandered ..).trans; apply mul_le_mul_of_nonneg_left _ h.W.fee
    apply (mul_le_mul (assistN (v 0).1 h.W.fund) (assistN (v 1).1 h.W.fund) (decay_pos ..).le (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add]; unfold flown aim exposed; congr 1; unfold timbre; simp only [v,chartB,show ∀ i,lift (wrap n (p i).1)=(p i).1 from he.2, show Laurent.size (0:Cover)=0 from by simp [Laurent.size],zero_add,Fin.sum_univ_two]; push_cast; ring
  rw [norm_zero]; exact mul_nonneg h.W.fee (aim_pos ..).le
lemma scanning (T:Cnr n→ℝ)(v: Fin 2→Cnr n): scanG T v=∑' p:Kite, (∏ i,v i (chartB (n:=n) p i))*scene T p:=by
  let Z (p:Fin 2→Road n): Kite:=fun i=> (Lattice.lift (p i).1,(p i).2)
  have hp p: chartB (n:=n) (Z p)=p:= by funext i; simp only [chartB,Z,wrap_lift]
  rw [tsum_eq_sum (s:=univ.image Z),sum_image (Function.LeftInverse.injective (show Function.LeftInverse (chartB (n:=n)) Z from hp)).injOn]; swap
  · intro b hb; unfold scene; split; swap; · rw [mul_zero]
    next h=> rw [Sparks.standing] at h; exact False.elim (hb (mem_image.mpr ⟨chartB b,mem_univ _,funext fun i=> Prod.ext (h.2 i) rfl⟩))
  have hh p : scene T (Z p)=Push.Uniform.entry T 0 p:=by
    have hm: AtMap n (exposed (Z p)):= (Sparks.standing _).mpr ⟨by unfold exposed; simp [lift],fun i=> congr_arg Lattice.lift (congr_arg (fun z:Fin 2→Road n=> (z i).1) (hp p))⟩
    rw [scene,if_pos hm,hp]
  simp_rw [hp,hh]; unfold scanG; nth_rw 1 [show v=(fun i=>∑ j:Road n,v i j • Push.Uniform.bolt j) from funext fun i=> bolt_add _]
  rw [blast]; refine sum_congr rfl fun p _=>?_ ; exact (iteratedFDeriv ℝ 2 T 0).toMultilinearMap.map_smul_univ _ _
abbrev Planet := Kite→ℝ
abbrev Skyline (S:SparkMesh):= (i:ℕ)→Cnr (S.n i) → ℝ
structure Heaven (S:SparkMesh)(T:Skyline S)(r C:ℝ)(P:Planet)(m:ℕ→ℕ):Prop where
 strict : StrictMono m
 converges (p:Kite): Tendsto (fun i=> scene (T (m i)) p) atTop (𝓝 (P p))
 ceiling (p:Kite): ‖P p‖≤ C*flown p r
lemma attainH (S:SparkMesh)(T:Skyline S)(hs:∀ i,Cigar (T i) r C):∃ P m,Heaven S T (r/4) C P m:=by
  let U (p:Kite): Set ℝ:= Metric.closedBall 0 (C*flown p (r/4)); have hp : IsCompact ((Set.univ:Set Kite).pi U):= isCompact_univ_pi fun _=> isCompact_closedBall ..
  obtain ⟨x,hx,m,hm,H⟩:= hp.isSeqCompact (show ∀ i:ℕ,scene (T i)∈(Set.univ:Set Kite).pi U from fun i j _=> mem_closedBall_zero_iff.mpr (scene_fit (hs i) j))
  exact ⟨x,m,hm,fun p=>tendsto_pi_nhds.mp H p,fun p=> mem_closedBall_zero_iff.mp (hx p (Set.mem_univ p))⟩
variable {S:SparkMesh}{T:Skyline S}{P:Planet}{m:ℕ→ℕ}
def lotusG (P:Planet)(x:Fin 2→Cnr n):=∑' p:Kite, (∏ i,idyllic (p i) (x i))* P p
def upLink (S:SparkMesh) (m:ℕ→ℕ)(i:ℕ)(x:Cnr (S.n i)) (j:ℕ): Cnr (S.n (m j)):= if h:i≤m j then expandC (S.vista i (m j) h) x else 0
lemma heavens (h:∀ i,Cigar (T i) r C)(hp: Heaven S T (r/4) C P m)(i:ℕ)(x:Fin 2→Cnr (S.n i)):
    Tendsto (fun j:ℕ=> scanG (T (m j)) (fun k=> upLink S m i (x k) j)) atTop (𝓝 (lotusG P x)):=by
  let V (j:ℕ)(k:Fin 2):Cnr (S.n (m j)):= if z:i ≤ m j then pacify (S.vista i (m j) z) (x k) else 0
  have hc:=hp.strict.tendsto_atTop.eventually_ge_atTop i
  refine Tendsto.congr' (f₁:=fun j=> scanG (T (m j)) (V j)) (hc.mono fun j he=>?_) ?_ -- order?
  · unfold V upLink; simp_rw [dif_pos he]; exact cigar_cut (h _) _ (fun k=> limitAt (x k) _)
  let d:=r/4; let B:= 16*‖x‖; have ht:0<d:=div_pos (h i).W.fund (by norm_num); have hC := (h i).W.fee
  simp_rw [scanning]; refine tendsto_tsum_of_dominated_convergence ((home_run ht).mul_left (B^2*C)) (fun p=> ?_) ?_
  · refine Tendsto.mul (tendsto_finsetProd _ fun k _=> tendsto_const_nhds.congr' ?_) (hp.converges p)
    filter_upwards [hc, chargeNext S hp.strict (p k).1,chargeNext S hp.strict ((p k).1+ step (axisEquiv.symm (p k).2.1))] with j hJ hL hk; unfold V; rw [dif_pos hJ]; exact (isp (S.vista i (m j) hJ) (x k) (p k) (into ..) hL hk).symm
  filter_upwards [hc] with j hJ p; unfold V; simp_rw [dif_pos hJ]; rw [norm_mul, norm_prod]
  have hx (k:Fin 2): ‖(pacify (S.vista i (m j) hJ) (x k) (chartB (n:=S.n (m j)) p k))‖ ≤ B*(1+timbre (exposed p)) :=by
    apply (spend_axis _ (x k) (p k)).trans; rw [mul_right_comm]; unfold B; gcongr; exacts [norm_le_pi_norm x k, (single_le_sum (fun k _=> Nat.zero_le (Laurent.size (p k).1)) (mem_univ k)).trans (Nat.le_add_left ..)] -- inspect
  apply (mul_le_mul (prod_le_prod (s:=univ) (fun k _=>norm_nonneg _) (fun k _=>hx k)) (scene_fit (h _) p) (norm_nonneg _) ((prod_nonneg fun k _=>by positivity))).trans_eq; rw [prod_const,card_univ,Fintype.card_fin]; unfold d; ring
end YM.QCD.Smoke
