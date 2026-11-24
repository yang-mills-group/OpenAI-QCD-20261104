import YM.QCD.King.Dealer
/-! # sell by ratio Brush and actual residual. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kings
open Finset RG Filter Function Lattice Wilson ConnectedActivityE6 Blaze Coat Metric
open Fork Lat Loom Fleet Kit Port Jets Run Brush Tidings Cove Sun Beam Pipe King Eider
open Extra Blaze.Vine Push Push.AbsoluteSums Footprint Pressure Stores Tree SectorMeasure Leaf Flume Pine Touch
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Classical ContDiff
variable {ι:Type}{c:Side}{V : Type}[NormedAddCommGroup V][NormedSpace ℝ V]{U:V → Grid c} {x:V}{k b B n:ℕ}{p a η w W:ℝ}
variable {H:St c}{G:Land c (Site c) (Site c)}{Y:Pays c (Site c) (Site c)}{s z ξ Λ μ C:ℝ} {f L:Side}{S:StepData c f}{P:Teller su}
variable {Q:Target su P}{o:Target.Order su W}
-- scale long materials by >cost bump OPTIONAL
noncomputable def tailTax (P:ι→ Prop)[DecidablePred P](v:ι→ℝ) (z:ℝ): ι→ℝ:=fun i=> if P i then z*v i else v i
lemma buyS (Γ:Target su P) (K η b r p:ℝ)(G D :ℕ)(hp:0< η)(hθ:0<b) (hw:b<1/8) (hu:0 ≤ r) (ha: p>r)(L:Side){V M:ℝ → ℝ}(Z:ℝ)(hh:1≤K)(C:ℝ)(M':ℕ)(μ:ℝ)(he: Rate su L (-(1/2)) M)(hf: Rate su L (-(1/2)) V) (hk:reserve r Γ.relative (10*preCost 37) 1) (o:Target.Order su W) :∀ᶠ z in atTop,
  let m:=radiusB z; let w:=highW L K b z; let Z:= coreRate L z
  ∀ (c f:Side) (S:StepData c f) (T: Tube su S)(R:Rep su f)(u:St c)(g:Land c (Site c) (Site c))(p':Pays c (Site c) (Site c)), S.patch.L=L → Pack id id η p M' u C g p' → ∀ (Y:ℝ)(J:Cash W z μ L Γ o Y T R),∀ χ A, Woods P L (2*o.a) M z →0≤V z →
   let U:= sailP J g G; let w' i:=posR D*glaze p' Z w G m i
   Honest U A 1 (fan L (1/4) z) w' w (V z) χ D Prod.fst (univ.filter fun i=>i.2=none) (18*m) 1 ∧
   Ac.Hit U.ground m (tailTax (fun i=>i.2≠none) w' (betaF su z L^(2:ℕ))) Γ.relative (2*betaF su z L^(-(3/8):ℝ)) :=by
    let v:= highW L K b; let q:= coreRate L
    have hv:Rate su L 0 v:= Rate.mul_left (Rate.rpow_monitor _) K
    let f x:=utt C (radiusB x) M' p r G (v x)
    let f' x:= q x*Real.exp r+f x
    have hx(t:ℝ):Rate su L t f:=by
       have hz : Rate su L t (fun i=> Real.exp (-(p-r)*fossil (radiusB i) M')):= Touch.pale p r ha M'
       exact (((hv.pow 2 |>.mul_right _).mul (hz.mul_right C |>.mul_left 4))).weaken (by linarith)
    have hx':Rate su L (-(2/5)) f':=(Rate.power.mul_right _).add (hx _)
    have hg : Seat L 0 (fun i=> Jets.Sun.rem 1 37 (radiusB i) Γ.relative 1 1):=by
      unfold rem Footprint.payment degreeIncome; simp only [Footprint.spread,extentCost,Nat.cast_mul]; exact ((expensed (L:=L) 0 (37+20) 0).timesL _|>.timesL _|>.times _|>.times _)
    let B x:=betaF su x L^(2:ℕ); let W₁ x:= rem 1 37 (radiusB x) Γ.relative (f' x) 1; let W₂ x:= rem 1 37 (radiusB x) Γ.relative (0*Real.exp r+f x) 1
    have hV : Rate su L (-(2/5)) (fun i=>posR D*W₁ i):=by unfold W₁; apply Rate.mul_left; simp_rw [leeway 1 (f' _)]; exact (hg.ruled.mul hx').weaken (by linarith)
    have hE: Rate su L (-1) (fun i=> B i*(posR D*W₂ i)):=by unfold W₂; simp_rw [zero_mul,zero_add, leeway 1 (f _)]; exact ((Rate.hat (G:=su) (L:=L)).pow 2|>.mul ((hg.ruled.mul (hx (-3))).mul_left _)).weaken (by norm_num)
    let K' t:= (1+(massQ+massQ))*V t; have hR:= hf.mul_left (1+(massQ+massQ)); let F x:=knock D η (V x); have hF : Rate su L (-(1/2)) F:=hR.mul_left _
    have hD :Rate su L (-(1/2)) (fun i=>F i*(v i^2*fingers G^2*(4*C))):= (hF.mul ((hv.pow 2|>.mul_right _).mul_right _)).weaken (by norm_num)
    obtain ⟨d,hd,H⟩:= halo_chart
    let s i:= d * (L.val*M i); have he': Rate su L (-(1/2)) s:= (he.mul_left (L.val:ℝ)).mul_left d
    have hA :Rate su L (-(1/2)) (fun i=>v i^2*fingers G^2*(4*s i/(η/2)*C)):=by simp_rw [div_eq_mul_inv (4*_ :ℝ)]; exact ((hv.pow 2 |>.mul_right _).mul (((he'.mul_left 4).mul_right _).mul_right _)).weaken (by norm_num)
    filter_upwards [hx'.below (by norm_num) 1 zero_lt_one, hV (-(3/8)) (by norm_num),hE (-(3/8)) (by norm_num),hR.below (by norm_num) 1 zero_lt_one,hF.below (by norm_num) 1 zero_lt_one,hD (-(2/5)) (by norm_num),he'.below (by norm_num) (η/3) (by positivity), hA (-(2/5)) (by norm_num), Port.crop_cost L G 0 (2*C) 0 K hθ hw, Work.E01.radiusB_tendsto.eventually_ge_atTop (M'+L.val+1),Delay.shift_pos su L] with x h h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hX hZ
    intro m w Z c f S T R u g p' hL ht Y J χ A hp' hU U w';
    have he: (S.ratio.count.val+1 ≤ radiusB x):= by rw [show S.ratio.count=L from hL]; omega
    have hM :0 < m:=by unfold m; omega
    have hT : 0 <w:=mul_pos (zero_lt_one.trans_le hh) (Touch.fan_pos ..)
    have hZ':0 < Z := Real.rpow_pos_of_pos hZ _; let K₀ (z:ℝ) i:=glaze p' z w G m i
    have hK a (ha:0≤a) i : 0≤K₀ a i:=by unfold K₀ glaze; split; exact ha; exact galaN ht ..
    have hu'(a:ℝ)(h:0 ≤ a):= fleets ht a G m w h (show M'≤ m from by unfold m; omega) ha.le hu
    have hM' :∀ i, K₀ Z i ≤1:=fun i=>(anchored_each Prod.fst (K₀ Z) _ (hu' Z hZ'.le) hu (hK Z hZ'.le) i).trans ((le_abs_self _).trans h)
    refine ⟨launchL J ht hp hT (hu.trans_lt ha) hU Z M A χ hZ' hp' d hd H (by omega) ((le_abs_self _).trans h₆ |>.trans_lt (by linarith)) ((le_abs_self _).trans h₇) hM' ((le_abs_self _).trans h₃) ((le_abs_self _).trans h₄) ((le_abs_self _).trans h₅) ((show _ from (by rw [show (4:ℝ)*C=2*(2*C) by ring,← show (_:ℝ)=0 from mul_zero (↑G*AtomF.rays*2)]; exact h₈))),?_⟩ -- edit
    have ht₀ z (hz:0≤z):= gameP J u g G m rfl _ (K₀ z) he hM (hu' z hz) hk (hK z hz)
    intro i
    let F:= betaF su x L ^ (-(3/8):ℝ); have hh:0≤posR D:= (Real.exp_pos _).le.trans (pos_bar ..); let v':=fun i=>B x*(posR D*K₀ 0 i)
    have hq:= heights_factor (posR D) _ _ _ (ht₀ Z hZ'.le) (show ∀ i, w' i=_ from fun _=>rfl) hh
    have hf:= heights_factor (B x) _ _ _ (heights_factor (posR D) _ _ _ (ht₀ 0 (le_refl _)) (show ∀ i,posR D*K₀ 0 i=_ from fun i=>rfl) hh) (show ∀ i,v' i=_ from fun _=>rfl) (by unfold B; positivity)
    rw [two_mul]; apply budget_mono (budget_plus (budget_loosen (hq i) (show _ ≤ F from (le_abs_self _).trans h₁)) (budget_loosen (hf i) ((le_abs_self _).trans h₂)))
    · intro j; split; swap; · exact le_rfl
      apply mul_nonneg _ (Real.exp_pos _).le; unfold tailTax; split; exact mul_nonneg (by positivity) (mul_nonneg hh (hK Z hZ'.le _)); exact mul_nonneg hh (hK Z hZ'.le _)
    intro j; by_cases ht:i∈U.ground j
    · change (if i∈ U.ground j then _ else _) ≤ (if i∈ U.ground j then _ else _)+(if i∈ U.ground j then _ else _); rw [if_pos ht,if_pos ht,if_pos ht]
      have ha:0≤ w' j:=mul_nonneg hh (hK Z hZ'.le j)
      unfold tailTax; split
      next h=> rw [show v' j=B x*w' j from (congr_arg (fun s=> B x*(posR D*s)) ( (show K₀ 0 j=_ from if_neg h).trans (show K₀ Z j=_ from if_neg h).symm))]; exact le_add_of_nonneg_left (mul_nonneg ha (Real.exp_pos _).le)
      apply le_add_of_nonneg_right; exact mul_nonneg (mul_nonneg (by unfold B; positivity) (mul_nonneg hh (hK _ le_rfl _))) (Real.exp_pos _).le
    simp_rw [if_neg ht]; exact add_nonneg ((hq i).1 j) ((hf i).1 j)
end YM.QCD.Kings
