import YM.Bank.Pilot
/-! grid quadratures with corners and punctures -/
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Pap
open Function Lattice Laurent Bloch Metric Precision MeasureTheory Filter
open Finset Pilot
open QCD.Pearl (beamP beam0 beamH ix)
open scoped Topology BigOperators ENNReal Matrix.Norms.L2Operator
variable {c:Side}{σ:Bool} {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
lemma bill (c:Side):c.val*beamH c=2*Real.pi:=by unfold beamH; field_simp
lemma limit_size (c:Side): beamH c≤ 2*Real.pi:=by unfold beamH; exact div_le_self (by positivity) (by exact_mod_cast c.property)
def coast : Set E4:= {x|∀ i, |x i|< Real.pi}
def mesa := ball (0:E4) (5*Real.pi)
lemma bounded {x:E4}{p:Site c}(h: x ∈ place σ p) : x ∈ mesa :=by -- implicit fix
    rw [mesa,mem_ball,dist_zero_right]; have hp := place_far h; rw [dist_eq_norm] at hp
    have hx:= norm_sub_norm_le x (earth (grid σ p)); have ht:=Pilot.pace (cubic σ p).1; have hv:=QCD.Pearl.cap_base (cubic σ p)
    linarith [limit_size c,Real.pi_pos]
lemma inland_f (σ:Bool){x:E4}(h:x∈coast):∀ᶠ c:Side in atTop,∃ p:Site c,x∈place σ p:=by
    have ht : ∀ i:Axis,∀ᶠ c : Side in atTop, |x i|+4*beamH c<Real.pi:=by
      intro i; have he:Tendsto (fun c:Side=>|x i|+4*beamH c) atTop (𝓝 (|x i|)):=by simpa using! (tendsto_const_nhds (x:= |x i|)).add (beam0.const_mul (4:ℝ)) -- arguments?
      exact he.eventually (gt_mem_nhds (h i))
    filter_upwards [eventually_all.mpr ht] with n hn
    let T:= beamH n; have hm:0<T:=beamP _
    let a : Cover:= fun i => Int.ceil (x i/T-κ σ - (1/2:ℝ))
    have he i: ((a i:ℝ)+ κ σ)*T-T/2<x i∧ x i ≤ ((a i:ℝ)+κ σ)*T+T/2:=by
        obtain ⟨hp,h⟩:= Int.ceil_eq_iff.mp (show ⌈x i/T-κ σ-1/2⌉ = a i from rfl); push_cast at hp
        constructor
        · have he:= (lt_div_iff₀ hm).mp (show (a i:ℝ)+κ σ-1/2 < x i/T by linarith); linarith
        have he:= (div_le_iff₀ hm).mp (show x i/T≤ (a i:ℝ)+κ σ+ 1/2 by linarith); linarith
    have hx : lift (wrap n a)=a:=by
        have hp : -1/2*T≤κ σ*T∧ κ σ*T≤0 :=by cases σ <;> simp [κ,hm.le] <;> linarith
        have hT : (n.val:ℝ)*T=2*Real.pi:=bill n
        apply lift_eq_iff.mpr; refine ⟨rfl,fun i=>?_⟩; obtain ⟨h₁,h₂⟩:=he i; have h₃:= hn i; change _+4*T <_ at h₃
        constructor
        · have hi : -(n.val:ℝ) < 2*(a i:ℝ):= lt_of_mul_lt_mul_right (a:=T) (by nlinarith only [hT,h₂, hp.2, neg_le_abs (x i), h₃,hm]) hm.le
          exact_mod_cast hi
        have hi : 2*(a i:ℝ) ≤ n.val:= le_of_mul_le_mul_right (a:=T) (by nlinarith only [hT,h₁,hp.1, le_abs_self (x i), h₃,hm]) hm; exact_mod_cast hi
    refine ⟨wrap n a, atPlace.mpr fun i=>?_⟩; rw [brick,hx]; exact he i
lemma sailing (σ:Bool){x:E4}(h: ∃ i, Real.pi< |x i|):∀ᶠ c:Side in atTop, ∀ p:Site c,x∉place σ p:=by
   obtain ⟨i,hi⟩:=h; filter_upwards [beam0.eventually (gt_mem_nhds (show 0< |x i|-Real.pi by linarith))] with c hc
   intro p hp; change beamH c< _ at hc; have he:= place_far hp; have hv: ‖x i - earth (grid σ p) i‖≤ beamH c:= (PiLp.norm_apply_le (x - earth (grid σ p)) i).trans ((dist_eq_norm x (earth (grid σ p))) ▸ he)
   rw [Real.norm_eq_abs] at hv; have h₁:|earth (grid σ p) i|≤ Real.pi:= (cubic _ _).2 i; linarith [(abs_sub_abs_le_abs_sub (x i) _).trans hv] -- lemma

open scoped Classical in
def wing (n:Side)(σ:Bool)(f:E4→V)(x:E4) := ∑ p:Site n,(place σ p).indicator (fun _=> f (earth (grid σ p))) x
lemma wing_place (f:E4→V){p:Site c}{x:E4}(h:x∈place σ p): wing c σ f x=f (earth (grid σ p)):=by
   rw [wing,sum_eq_single p, Set.indicator_of_mem h]
   intro j _ hj; apply Set.indicator_of_notMem; exact fun g=>Set.disjoint_left.mp (canopy_dis _ (univ: Finset (Site c)) (mem_univ j) (mem_univ p) hj) g h -- p inferred?
   simp
lemma wing_no (f:E4→V){x:E4} (h:∀ p:Site c,x∉place σ p): wing c σ f x=0:=sum_eq_zero fun p _=> Set.indicator_of_notMem (h p) _
lemma wing_grants (f:E4→V)(σ:Bool)(c:Side): Integrable (wing c σ f) volume ∧ ∫ x,wing c σ f x= ∑ p:Site c,(beamH c^4) • f (earth (grid σ p)):=by
   classical
   have ht (p:Site c) : volume (place σ p)≠⊤:=by rw [parcel]; exact ENNReal.ofReal_ne_top
   let g (p:Site c) (x:E4):=(place σ p).indicator (fun _=> f (earth (grid σ p))) x
   have hx (p:Site c): Integrable (g p):= (integrableOn_const (ht p)).integrable_indicator (placeM ..) -- default measure
   refine ⟨integrable_finsetSum _ (fun p _ => hx p),?_⟩
   change ∫ x,∑ p:Site c,g p x = ∑ p:Site c,_
   rw [integral_finsetSum _ (fun p _=>hx p)]
   apply sum_congr rfl; intro p _; rw [show (g p)=(place σ p).indicator _ from rfl,integral_indicator (placeM ..),setIntegral_const,parcelV]

lemma pole_rpw {x:E4}(h:x≠0): ‖x‖⁻¹= ‖x‖^(-(1:ℝ)):=by rw [Real.rpow_neg (norm_nonneg _),Real.rpow_one]
lemma pole_sky : IntegrableOn (fun x:E4=> ‖x‖⁻¹) mesa :=by
   have hm:Measurable (fun x:E4=> ‖x‖⁻¹):=continuous_norm.measurable.inv
   apply integrableOn_ball_of_norm_le_rpow (hd:= by norm_num [E4,Axis]) (show (1:ℝ)<Module.finrank ℝ E4 by norm_num [E4,Axis]) (C:=1) ?_ hm.aestronglyMeasurable
   apply Eventually.of_forall; intro x; simp [Real.rpow_neg (norm_nonneg x)]
open scoped Classical in
def sky (C:ℝ): E4→ℝ:=mesa.indicator fun x=> (8*C)*‖x‖⁻¹
lemma sky_i (C:ℝ): Integrable (sky C):= IntegrableOn.integrable_indicator (Integrable.const_mul pole_sky _)  measurableSet_ball
lemma sky_pos {C:ℝ}(h:0≤C):∀ x,0≤sky C x:=by
   intro x; unfold sky; by_cases hx:x∈mesa; rw [Set.indicator_of_mem hx]; positivity; rw [Set.indicator_of_notMem hx]
lemma wing_cost {K:ℝ} (hK:0≤K)(σ:Bool)(c:Side)(f:E4→V)(h:∀ i:Site c,‖f (earth (grid σ i))‖≤ K / ‖grid σ i‖): ∀ x:E4,x≠0→‖wing c σ f x‖≤sky K x:=by
   intro x hx
   by_cases hp: ∃ p:Site c,x∈place σ p; swap; · rw [wing_no f (not_exists.mp hp),norm_zero]; exact sky_pos hK x
   obtain ⟨p,hp⟩:=hp; rw [wing_place f hp]; refine (h p).trans ?_; by_cases he:grid σ p=0
   · rw [he,norm_zero,div_zero]; exact sky_pos hK x
   rw [sky,Set.indicator_of_mem (bounded hp)]; have ht:=pole_length σ p he; have hv:= Pilot.pace (cubic σ p).1; have hm:= norm_pos_iff.mpr hx; have hs:= place_far hp; rw [dist_eq_norm] at hs
   have hl: ‖x‖ ≤ 8*‖grid σ p‖ := by linarith [norm_sub_norm_le x (earth (grid σ p)), norm_nonneg (grid σ p)]
   rw [← div_eq_mul_inv,div_le_div_iff₀ (norm_pos_iff.mpr he) hm]; exact (mul_le_mul_of_nonneg_left hl hK).trans_eq (by ring)
end YM.Bank.Pap
#print axioms YM.Bank.Pap.wing_cost
#print axioms YM.Bank.Pap.inland_f
