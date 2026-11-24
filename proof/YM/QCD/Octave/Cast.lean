import YM.QCD.Octave.Day
/-! # Bootstrapping Pennant marks. Error o(β^-1) even at all sunset window.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Octave
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam Cove Golden NormedSpace
open scoped Topology ENNReal ContDiff BigOperators Classical
open Lat YM.Next.Free Reggae
open Jets.Touch Port Kit Run Stew Bay Strut Leaf Tee Flume Garden Kings Orbit LeafM Oasis
open scoped Matrix.Norms.L2Operator
variable {L:Side}{w z u y p:ℝ→ℝ}{A a b R D η M N H W K v s t:ℝ} {j i l:ℕ}
local notation "g"=>coneK L a
lemma flipE (hx:0<a):Rate su L (1/16) (fun x=>(g x)⁻¹):=by
   refine ((shade_e L hx.ne').mul_right (2:ℝ)⁻¹).congr (Eventually.of_forall fun i=>?_); dsimp only; rw [div_eq_mul_inv, _root_.mul_inv_rev]; ring_nf
lemma pitchB (he:0<a)(j:ℕ) : Rate su L ((1/16)*j) (fun x=> Kit.toll (g x) j):=by
    induction j with
    | zero=> simpa only [Kit.toll,Nat.cast_zero,mul_zero] using Rate.const (L:=L) (G:=su) 1
    | succ k ih=> refine ((ih.mul ((flipE he).mul_left (2^(k+1)))).weaken (by push_cast; linarith)).congr ?_; refine Eventually.of_forall fun i=>?_ ; dsimp only; rw [Kit.toll,div_eq_mul_inv, div_eq_mul_inv,_root_.mul_inv_rev,_root_.inv_inv]
lemma noteF (ht:0<a)(j:ℕ)(R Z:ℝ): Rate su L ((1/16)*j) (fun x=> noteC (g x) R Z j):=by
    have he(k:ℕ): Rate su L ((1/16)*k) (fun x=> letterP (g x) k):=by
       induction k with
       | zero=> simp only [letterP,zero_add, Finset.sum_range_one,Kit.toll,Nat.cast_zero,mul_zero]; exact Rate.const _
       | succ k ih=> apply ((ih.weaken (by push_cast; linarith)).add (pitchB ht (k+1))).congr; exact Eventually.of_forall fun i=> Finset.sum_range_succ ..
    unfold noteC clump; exact (((he j).mul_right _).mul_left _).mul_right _
lemma roofF (ht:0<a)(j:ℕ)(N:ℕ)(Z R A:ℝ)(hw:Seat L s w)(hz:Seat L t z)(hu:Seat L v u):Rate su L (1/16*j) (fun x=> gross Z (g x) R A (w x) (z x) (u x) j N):=by
    let f x:= w x * Fintype.card Lat.Fiber
    have h: Rate su L 0 f:=hw.ruled.mul_right _
    unfold gross; have hv := Brim.bell (Brim.prep hu.ruled 2) (Brim.prep hz.ruled 2)
    exact ((((h.mul (noteF ht j A Z)).weaken (by linarith)).add ((h.mul_right _).weaken (by positivity))).mul_left _|>.add ((hv.mul (noteF ht j R Z)).weaken (by linarith)))
lemma roofF' (V:ℝ)(j N:ℕ)(Z R A:ℝ)(hw:Seat L 0 w)(hz:Seat L 0 z)(hu:Seat L v u)(he:0<v) : Seat L (v*2) (fun x=>gross Z V R A (w x) (z x) (u x) j N):=by
    have hp:= hw.times (Fintype.card Lat.Fiber); unfold gross; apply Seat.comb
    · apply Seat.timesL; exact (((hp.times _).comb (hp.times _)).above (by positivity))
    apply Seat.times; exact (((hu.powered 2).ponies (hz.powered 2)).above (by push_cast; linarith))
lemma mansF (N:ℕ)(A R:ℝ)(hw:Seat L 0 w)(hz:Seat L 0 z)(hu:Seat L v u)(he:0<v):Seat L (v*2) (fun i=>fundsX (w i) (z i) (u i) A R N):=by
   have h:= (hw.times (Fintype.card Lat.Fiber)).times A; unfold fundsX; exact (((h.comb h).above (by positivity)).timesL _|>.comb ((((hu.powered 2).ponies (hz.powered 2)).above (by push_cast; linarith)).times _))
lemma pants {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{U:E → F}(h:0<b)(hx:∀ x, ‖x‖<b → Brush 3 R 1 U x)(hp:R*b≤K){z:E}(hz: ‖z‖<b)(ht:normJ 2 U 0 ≤A): normJ 2 U z≤ A+K:=by
   let u:= ball (0:E) b; let V:=iteratedFDeriv ℝ 2 U; have hh(z:E)(hz:z∈u): DifferentiableAt ℝ V z:=(hx z (mem_ball_zero_iff.mp hz)).smooth.differentiableAt_iteratedFDeriv (by norm_cast)
   have hf(z:E)(hz:z∈u): ‖fderiv ℝ V z‖≤R := norm_fderiv_iteratedFDeriv.trans_le ((Brush.offer.mp (hx z (mem_ball_zero_iff.mp hz))).2 3 le_rfl)
   have ht':=(convex_ball (0:E) b).norm_image_sub_le_of_norm_fderiv_le hh hf (mem_ball_self h) (mem_ball_zero_iff.mpr hz)
   exact (norm_le_norm_add_norm_sub' (V z) (V 0)).trans (add_le_add ht (ht'.trans ((mul_le_mul_of_nonneg_left (show ‖z-0‖ ≤ b from by simpa using hz.le) (hx z hz).nonneg).trans hp)))
lemma skyCost (h :0<a)(ht:0<v)(he:Seat L 0 w)(hz:Seat L 0 z)(hu:Seat L v u)(hp:Rate su L vow p)(hP:∀ᶠ x in atTop,0<p x)(Z:ℕ→ℝ)(N k:ℕ)(R A:ℝ):
    let V x i:= gross (Z i) (g x) R A (w x) (z x) (u x) i N
    ∀ᶠ x in atTop,p x ≤ 1 ∧ V x 3 *p x≤1 ∧∀ i:ℕ, 3 ≤ i → i≤k→ V x i * (p x)^i ≤ (p x)^2 :=by
   intro V; have h₃:= roofF h 3 N (Z 3) R A he hz hu
   have hh(i:Fin (k+1))(hi: 3 ≤ i.val): ∀ᶠ x in atTop,V x i*(p x)^i.val ≤(p x)^2:=by
      have hr:= ((roofF h i N (Z i) R A he hz hu).mul (hp.pow (i.val-2))).below (by unfold vow; rw [Nat.cast_sub (by omega : 2 ≤ i.val)]; push_cast; have hh':(3:ℝ)≤ i.val:= (by exact_mod_cast hi); nlinarith) _ zero_lt_one
      filter_upwards [hr,hP] with x hx he; have hf :V x i*(p x)^(i.val-2) ≤ 1:= (le_abs_self _).trans hx
      rw [← mul_le_mul_iff_of_pos_right (pow_pos he 2)] at hf; rw [mul_assoc,← pow_add,Nat.sub_add_cancel (by omega),one_mul] at hf; exact hf
   have he' : ∀ᶠ x in atTop, ∀ i:Fin (k+1),3 ≤ i.val → V x i*(p x)^i.val ≤(p x)^2 := eventually_all.mpr fun i=>by
     by_cases h:3 ≤ i.val; · exact (hh i h).mono fun x hx _=> hx
     exact Eventually.of_forall fun x hx=>(h hx).elim
   filter_upwards [Sienna.below' su L hp vow_ok zero_lt_one,(h₃.mul hp).below (by norm_num [vow]) _ zero_lt_one,he'] with x hx hh ht
   exact ⟨hx.le,(le_abs_self _).trans hh,fun i h he=> ht ⟨i,by omega⟩ h⟩
end YM.QCD.Octave
