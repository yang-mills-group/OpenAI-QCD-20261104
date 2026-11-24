import YM.QCD.Pearl.Tilts

/-! # true torus tiles on annulus for momentum test -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Flume Laurent Bloch Metric YM.Next.Free RG Rudder Free Para Pinch MeasureTheory Stationary
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff ENNReal
variable {n: Side} {κ : ℝ}
abbrev atomR (p : Site n):=‖centerZ p‖

def smallH (n:Side)(t:ℝ): Finset (Site n):=by classical exact univ.filter fun i=> atomR i ≤ t*beamH n
def midst (n:Side)(t:ℝ): Finset (Site n):=by classical exact univ.filter fun i=> i∉smallH n t ∧ atomR i<1/2
lemma small_h {p:Site n}: p ∈ smallH n κ↔ atomR p≤κ*beamH n:=by classical simp [smallH]
lemma medium {p:Site n}:p∈midst n κ↔ κ*beamH n<atomR p∧atomR p<1/2:=by classical simp[midst,small_h]
def fans (t:Finset (Site n)):= ⋃ p∈t,seat p
lemma fans_m (A:Finset (Site n)):MeasurableSet (fans A):= by unfold fans; exact Finset.measurableSet_biUnion _ fun i _=> chair _ -- inspect
lemma fan_spec {A:Finset (Site n)}(x : Gₐ):x∈fans A ↔ ∃ i∈A,x∈seat i:=by simp [fans]
lemma fans_dis (A:Finset (Site n)):Set.PairwiseDisjoint (A : Set (Site n)) seat:= fun _ _ _ _ he=> Set.disjoint_left.mpr fun _ h hk=> he (order_eq h hk)
lemma fans_vol (A: Finset (Site n)):volume.real (fans A)= (A.card:ℝ) *(beamH n)^4:=by
  unfold fans; rw [measureReal_biUnion_finset (fans_dis A) (fun i _=>chair i) (fun i _=>by rw [seating]; exact ENNReal.ofReal_ne_top)] 
  simp_rw [seatVolume]; simp
lemma row_count (ht : 3≤κ): ((smallH n κ).card:ℝ) ≤ ((κ+1)^4)*(Real.pi^2/2):=by
  let t:=beamH n
  have hL:=beamP n; have hp:0<t:=hL
  let A:=smallH n κ
  let S:=fans A
  have hx:S ⊆ closedBall (0:Gₐ) ((κ+1)*t):=by
    intro x hv
    obtain ⟨i,hv,h⟩:= (fan_spec x).mp hv; rw [mem_closedBall,dist_zero_right];
    have hi: ‖centerZ i‖≤ κ*t :=small_h.mp hv; have he :‖x-centerZ i‖ ≤ t:= by rw [← dist_eq_norm]; exact seat_far h
    linarith [norm_sub_norm_le x (centerZ i)]
  have he:=measureReal_mono (μ:=volume) hx (isCompact_closedBall ..).measure_ne_top
  change volume.real (fans A) ≤ _ at he; have hb:0<κ+1:= by linarith
  rw [fans_vol,solidGaia (mul_nonneg hb.le hp.le)] at he
  apply le_of_mul_le_mul_right _ (pow_pos hp 4); exact he.trans_eq (by unfold t; ring)
lemma seat₃ (ht:beamH n≤1/4){p:Site n}(h:3≤κ)(hp:p∈midst n κ):seat p⊆orbShell (beamH n):=by
  intro v hv; have hz:=beamP n; obtain ⟨hy,hP⟩:= medium.mp hp
  have hh:=seat_far hv; rw [dist_eq_norm] at hh
  unfold atomR at *; refine ⟨?_,?_⟩
  · linarith only [mul_le_mul_of_nonneg_right h hz.le,hy,hh,hz,norm_sub_norm_le (centerZ p) v,norm_sub_rev v (centerZ p)]
  linarith only [hP,ht,hh,norm_sub_norm_le v (centerZ p)]
lemma inn (ht:beamH n≤1/4)(h:3≤κ): fans (midst n κ)⊆orbShell (beamH n):= fun v hv=> by obtain ⟨i,he,hi⟩:=(fan_spec v).mp hv; exact seat₃ ht h he hi
lemma between (ht:beamH n<1/4)(h:3≤κ): orbShell ((κ+1)*beamH n) ∩ closedBall 0 (1/4) ⊆ fans (midst n κ):=by
  rintro x ⟨ha,hc⟩; obtain ⟨p,hp⟩:= seatingBall (n:=n) x ha.2 (by linarith); refine (fan_spec _).mpr ⟨p, medium.mpr ⟨?_,?_⟩,hp⟩
  all_goals rw [mem_closedBall,dist_zero_right] at hc; have he:=seat_far hp; rw [dist_eq_norm] at he; unfold atomR; have hh: (κ+1)*beamH n<‖x‖:=ha.1
  · linarith [norm_sub_norm_le x (centerZ p)]
  linarith [norm_sub_rev x (centerZ p), norm_sub_norm_le (centerZ p) x]

def radial (n:ℕ)(x:Gₐ):= (‖x‖^n)⁻¹
lemma sinuous (x:Gₐ)(i:ℕ): 0≤ radial i x := by unfold radial; positivity
lemma sorb (m:ℕ){μ:ℝ}(h:0<μ): IntegrableOn (radial m) (orbShell μ) volume:=by simpa [radial] using! geoS h (fun _=>1) continuous_const m
lemma ripe {μ:ℝ}(h:0<μ)(he: μ≤1): ∫ x in orbShell μ,radial 5 x=2*Real.pi^2*(μ⁻¹-1):=by
  have hu : (0:ℝ)∉Set.uIcc μ 1:=by simp only [Set.uIcc_of_le he]; exact fun i=> h.not_ge i.1
  unfold radial; rw [shell_turn μ h he (fun x=> (x^5)⁻¹)]; congr 1; rw [intervalIntegral.integral_congr (g:=fun x:ℝ=>x^(-2:ℤ)), integral_zpow (n:=(-2:ℤ)) (Or.inr ⟨by norm_num,hu⟩)]
  · norm_num; field_simp [h.ne']; ring
  intro x hx; field_simp [show x≠0 from fun he=> hu (he ▸ hx)]
lemma compareCost (i:ℕ) (ht:beamH n≤1/4)(h:3≤κ): ∑ p ∈ midst n κ, (beamH n)^4 * radial i (centerZ p) ≤ (2:ℝ)^i * ∫ x in orbShell (beamH n), radial i x:=by
  let F:=fans (midst n κ); have he:=inn ht h; have hs:=beamP n; have hS:=sorb i hs; have hu := hS.mono_set he
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (setIntegral_mono_set hS ?_ (Eventually.of_forall he)) (show 0≤(2:ℝ)^i by positivity)) -- setIntegral_mono_set args inspect
  · change _≤2^i * ∫ x in fans (midst n κ),radial i x; rw [fans, integral_biUnion_finset _ (fun i _=> chair i) (fans_dis _) (fun _ hp=> hS.mono_set (seat₃ ht h hp)),Finset.mul_sum]
    apply sum_le_sum; intro i' hp; rw [← seatVolume i',← smul_eq_mul,← setIntegral_const,← integral_const_mul]
    refine setIntegral_mono_on ?_ ((hS.mono_set (seat₃ ht h hp)).const_mul _) (chair _) fun x hx=> ?_
    · apply integrableOn_const ?_ (hC:=by simp); rw [seating]; exact ENNReal.ofReal_ne_top
    have hx0 : beamH n<‖x‖:= (seat₃ ht h hp hx).1; have hi : κ*beamH n< ‖centerZ i'‖:= (medium.mp hp).1
    have hz:=seat_far hx; rw [dist_eq_norm] at hz
    have hh : beamH n ≤ ‖centerZ i'‖:=by nlinarith
    have hk : ‖x‖≤ 2*‖centerZ i'‖:=by linarith [norm_sub_norm_le x (centerZ i')]
    unfold radial; rw [← one_div, ← div_eq_mul_inv,div_le_div_iff₀ (pow_pos (hs.trans_le hh) _) (pow_pos (hs.trans hx0) _),one_mul,← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hk _
  exact Eventually.of_forall fun x=> sinuous ..
end YM.QCD.Pearl
