import YM.Shade.Ozone
import YM.Tarn.Spoil
/-! Mixed charges authentic transfer: near point tests and uniform slopes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Analysis YM.Fir Massive.Fir Fir YM.Fir.NoteF Fir.Gains Fir.TagF Zodiac Filter Set Metric
open Lattice Cells QCD QCD.Lat UV Lattice Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.CardsT Intag.Vale
open scoped Topology ContDiff BigOperators Classical
open Function Sash
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
namespace Choir
variable {Q: Choir}
variable (H:Q.Harmony P φ)
namespace Measures
set_option maxHeartbeats 720000
noncomputable def arm : E4 →L[ℝ] Points 2:= {
    toFun:= fun (x:E4)=> points ![0,x]
    map_add' :=by intro x y; change points _= (points ![0,x])+points _; apply PiLp.ext; intro i; fin_cases i; exact (zero_add 0).symm; rfl
    map_smul' :=by intro a x; change points _=a • points ![0,x]; apply PiLp.ext; intro i; fin_cases i; exact (smul_zero a).symm; rfl
    cont := by
         have ht: Continuous fun x:E4=> (![0,x]:Fin 2→E4):=continuous_pi fun i=> by fin_cases i; exact continuous_const; exact continuous_id
         exact (PiLp.continuous_toLp 2 _).comp ht }
lemma arm_l (x:E4) : arm x=points ![0,x]:=rfl
lemma axis_l (a:Axis): arm (basis a)=Points.direction 1 a:=by ext1 i; rw [arm_l]; fin_cases i <;> simp [Points.direction,PiLp.single_apply]
lemma forms {x:E4}(hx:x≠0): arm x∈conf 2:=by rw [arm_l]; intro i j h; change points ![0,x] i=points ![0,x] j at h; fin_cases i <;> fin_cases j <;> first|rfl|exact False.elim (hx h)|exact False.elim (hx h.symm)
variable (w v:Q.W)(a:Axis) (x:E4)
noncomputable abbrev ans2 (w v:Q.W)(x:E4):ℂ:= Q.total 2 (arm x) ![w,v]
variable {h:ℝ}
private lemma updates : (update ![w,v] 1 (Q.arc a v))=![w,Q.arc a v]:=by ext1 i; fin_cases i <;> simp
private lemma fern {E B:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B](T:E→L[ℝ]B)(x:E): fderiv ℝ (⇑T) x=T:=T.fderiv
lemma boundL (hx:x≠0) (H:Q.Domestic) : D (basis a) (ans2 w v) x= ans2 w (Q.arc a v) x:=by
    let f(p:Points 2):= Q.total 2 p ![w,v]; have hg: DifferentiableAt ℝ f (arm x):=((H.smooth _ _).contDiffAt ((conf_open _).mem_nhds (forms hx))).differentiableAt (by simp)
    unfold D; change fderiv ℝ (f∘arm) x _=_; rw [fderiv_comp x hg arm.differentiableAt, ContinuousLinearMap.comp_apply, show fderiv ℝ (⇑arm) x=arm from fern arm x, axis_l]; have ht := H.derivatives 2 (arm x) (forms hx) ![w,v] 1 a; rw [Matrix.cons_val_one,Matrix.cons_val_zero,updates] at ht; exact ht
private lemma strict (hx:x≠0)(H:Q.Domestic) : HasStrictFDerivAt (ans2 w v) (fderiv ℝ (ans2 w v) x) x:=((((H.smooth 2 ![w,v]).contDiffAt ((conf_open _).mem_nhds (forms hx))).comp (g:=fun z=>Q.total 2 z ![w,v]) x (arm.contDiff.contDiffAt)).hasStrictFDerivAt (by simp)) -- syntax
private lemma strictCn (x:E4)(f:E4→ℂ)(F:E4→L[ℝ]ℂ)(h:HasStrictFDerivAt f F x)(ε:ℝ)(he:0<ε):∃ δ:ℝ,0<δ ∧ ∀ z:E4,∀ t:ℝ,0<t→dist (z+t • basis a) x < δ → dist (z-t • basis a) x<δ → ‖(t⁻¹/2) • (f (z+t • basis a)-f (z-t • basis a))-F (basis a)‖ ≤ ε:=by
      have h:∀ᶠ p:E4×E4 in 𝓝 (x,x), ‖f p.1 - f p.2 - F (p.1-p.2)‖ ≤ ε*‖p.1-p.2‖ := (hasStrictFDerivAt_iff_isLittleO.mp  h).def he
      obtain ⟨δ,hδ,hK⟩:= Metric.mem_nhds_iff.mp h; refine ⟨δ,hδ,fun z t h0 hA hB=>?_⟩
      let p:= z+t • basis a; let q:= z-t • basis a; have hz:p-q=(2*t) • basis a:=by unfold p q; rw[two_mul,add_smul]; abel
      have hm: ‖f p-f q-F (p-q)‖ ≤ ε * ‖p-q‖ := hK (show (p,q)∈Metric.ball (x,x) δ by rw[Metric.mem_ball,Prod.dist_eq,max_lt_iff]; exact ⟨hA,hB⟩)
      let W:= f p- f q-F (p-q); change ‖(t⁻¹/2) • _ - _‖ ≤ _; have hV:t⁻¹/2*(2*t)=1:=by field_simp [h0.ne']; -- ring?
      have hr:(t⁻¹/2) • (f p - f q) - F (basis a)=(t⁻¹/2) • W:=by
          rw[show W= _ from (show W= f p- f q-F (p-q) from rfl), smul_sub (_:ℝ) (f p- f q) (F (p-q)),hz,map_smul,smul_smul,hV,one_smul]
      change ‖(t⁻¹/2) • (f p- f q) - _‖ ≤ ε; rw [hr,norm_smul,Real.norm_of_nonneg (half_pos (inv_pos.2 h0)).le]; refine (mul_le_mul_of_nonneg_left hm (half_pos (inv_pos.2 h0)).le).trans_eq ?_; rw [hz,norm_smul,basis_norm,Real.norm_of_nonneg (by positivity),mul_one,show t⁻¹/2 *(ε*(2*t))=(t⁻¹/2*(2*t))*ε from by ring,hV,one_mul]
lemma centred (hx:x≠0) (H:Q.Domestic)(ε:ℝ)(he:0<ε):∃ δ:ℝ,0<δ ∧ ∀ z:E4,∀ t:ℝ,0<t→dist (z+t • basis a) x < δ → dist (z-t • basis a) x<δ → ‖(t⁻¹/2) • (ans2 w v (z+t • basis a)-ans2 w v (z-t • basis a))-ans2 w (Q.arc a v) x‖ ≤ ε:=by
      rw [← boundL w v a x hx H]; exact strictCn a x _ _ (strict w v x hx H) ε he
end Measures
end Choir
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Choir.Measures.centred
