import YM.QCD.Oasis.Rip
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Purple
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Oasis
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Jets.Touch
open Cove
variable {σ C u v d w τ ξ B a ζ:ℝ}{K : KernelChoices} {P' : Teller su}{a':ℝ}{l n:ℕ}
variable {L:Side}{z m p f g:ℝ→ℝ} {U:ChartRatio su}
lemma spentE (hv: Seat L 0 m)(he:Seat L ξ f)(hz:0<ξ): Seat L ξ (fun x=>spanV (f x) (m x)):=by unfold spanV; apply Seat.comb; exact ((Seat.numbers _ |>.comb hv).above hz.le); exact he
lemma rideE (hv: Seat L 0 m)(he:Seat L ξ f)(hp:Seat L τ g)(hq:Seat L τ p)(h:0<ξ)(ht:0<τ)(j:ℕ):
    let u:= τ+ξ*2; Seat L u (fun i=>growT j (m i) (f i) (g i) (p i)) ∧ Seat L (2*u) (fun i=>dawnT j (m i) (f i) (g i) (p i)):=by
   intro u; let X i:=growT j (m i) (f i) (g i) (p i); have hu:0<u:=by unfold u; positivity
   have hh:=spentE hv he h; have hK:= hp.ponies (hh.powered 2); push_cast at hK
   let uK i:=clump j 2 (g i*(spanV (f i) (m i))^2); have hz : Seat L u uK:= (hK.timesL _).times _; have hm:Seat L u X:= (((hz.comb hz).comb ((hq.ponies he).above (by unfold u; nlinarith))).comb ((Seat.numbers _).above hu.le))
   exact ⟨hm, Seat.comb (((hm.powered 2).above (by push_cast; linarith : u* ↑(2:ℕ) ≤ 2*u)).times _) ((hz.comb hz).above (by linarith))⟩
lemma nextK (hv: Seat L 0 m)(he:Seat L ξ f)(hp:Seat L τ g)(hq:Seat L τ p)(hz:0<ξ)(j:ℕ):
    let Y x:= eaves su L x; let k:= j+2
    ∃ d:ℝ,0≤d ∧ ∀ᶠ x in atTop,roofT j (Y x) (keenR k (m x) (f x) (p x) (g x) (Y x)) ≤ betaF su x L^d:=by
    intro Y k; have hh:Rate su L 0 Y:= (edge su L).weaken vow_ok.le
    let f' i:=spanV (f i) (m i)*Y i; let p' i:=keenR k (m i) (f i) (p i) (g i) (Y i)
    have hf: Rate su L 0 f':=Brim.bell (spentE hv he hz).ruled hh; have hp: Rate su L 0 p':= (Brim.bell hq.ruled (hf.mul_right 2)).add (lumpRate k (Rate.const _) (Brim.bell hp.ruled ((hf.pow 2).weaken (by norm_num))))
    have he' : Rate su L (7/16) (fun x=>(Y x)⁻¹):= Rate.power.congr ((Delay.shift_pos su L).mono fun i hx=> by dsimp only [Y,eaves]; rw [show vow= -((7:ℝ)/16) by norm_num [vow],Real.rpow_neg hx.le,inv_inv])
    have hv':= hp.mul (((Rate.const 1 |>.weaken (by norm_num : (0:ℝ) ≤7/16)).add he').pow j); have hm:= (Token.climbF (hv'.add hv') (by positivity) j (strain j)).add ((Rate.const 1).weaken (by positivity)); let d:= (0+(7/16:ℝ)*j)*j+1; refine ⟨d,by unfold d; positivity,?_⟩; filter_upwards [hm d (by unfold d; linarith)] with i hi using (le_abs_self _).trans hi
lemma halfBill (v:ℝ)(hv: ξ < v)(hx:0 < v) (h:Seat L ξ f): ∀ᶠ x in atTop,Real.exp (f x+f x)+2 ≤ Real.exp (fan L v x):=by
   let A p:=fan L v p; have hm:Tame L fun i=>  (Real.exp (-(A i))*(Real.exp (f i+f i))+(Real.exp (-(A i)))*2):=by
      have hA:= joyP (h.comb h) zero_lt_one hx hv; unfold Tame
      refine fun i=> (((hA i).add ((narrowedP (L:=L) 1 v zero_lt_one hx rfl i).mul_right 2)).congr (Eventually.of_forall fun j=> by simp only [neg_mul,one_mul]; rfl))
   filter_upwards [(hm (-1)).below (by norm_num) _ zero_lt_one] with i h
   have hp:= (le_abs_self _).trans h; change Real.exp _+2≤Real.exp (A i)
   rwa [Real.exp_neg,← mul_add,inv_mul_le_one₀] at hp -- name
   exact Real.exp_pos _

-- purchase for auxiliary calculus income. Caller indirectly gets one manifest grant with W.N.
lemma litE (Q:Patch)(P:Teller su) (V:Before su σ C Q.J K ((l+1+2)+3))(coat: FiberFee U (((l+1+2)+3)+1))(clip: Clip)(Λ:ℝ) (s f w h g:ℝ → ℝ) (hs:Rate su Q.L 0 s)(hO:LocalRatio U) (hw:Bolt su Q.L w)(ht:Seat Q.L τ f)(hx:Seat Q.L τ h)(hq:Seat Q.L τ g) (he:0 < τ) (hr:τ<v)(hy:v<ξ)(hξ:ξ<1)(hp: amass (l+1) ξ (2*(τ+ξ*2)) < ζ)(hB: 0<B)(N:ℕ):
    ∀ᶠ t in atTop, let m:=pam (l+1+2) U clip Q V (w t) (w t) coat Λ; let L:= Q.L; let M:=fan Q.L ξ t; let u:= eaves su Q.L t
      ∀ (c b: Side)(S:StepData c b)(F:Forest S.ratio)(Y:Tube su S)(k:S.Choices) (eQ:S.patch=Q)(eK:S.kernel=K)(e:Y.high=clip)(Ω:BudgetPoint) (β:ℝ), Quilt Y F (w t) → Y.up.Bounds clip σ C Λ →
      ∀ (ρ:Bid.Dir su c→AxisChart su F), (Sienna.warm V eQ eK).Service F Y.high Y.up ρ → Intake P Y t (Pane.virgin Y Ω β) →∀ (Φ:F.Slice su→EvenA c N), TellerX (glimB Φ) (spanV M m) u (f t) (h t) (l+1+2) → Continuous Φ → (∀ i, ‖Φ i‖≤g t) → ∀ (x:Positions (Uniform.Primary c su)), LawP Y (Sienna.warm V eQ eK) Ω F ρ k Q.L U B (s t) t β x→ ‖x‖+furl su Q.L t<u → 0<tramp Y Ω β x ∧ Brush l (brass L t ζ) u⁻¹ (Sol (G:=su) (N:=N) β F Y Ω (heat Φ (Lapis.orbit F ρ))) x:=by
    let L:= Q.L; let M t:=fan L ξ t; let m t:=pam (l+1+2) U clip Q V (w t) (w t) coat Λ; have hq':=he.trans hr; have hζ:=hq'.trans hy; let k:=l+1+2
    let R:= V.tables clip Q; by_cases hh :0<R.gap
    swap
    · refine Eventually.of_forall ?_; intro t m L M' u c b S F Y k eQ eK e Ω β hC hJ ρ he
      subst Q; subst K; subst clip; exact False.elim (hh (V.receipt F k hJ hC.large rfl rfl).1.pos_m)
    have hh' :Seat L 0 m:=parksX V coat _ hw Λ
    have hM: Seat L ξ M:=Seat.keeps
    obtain ⟨hA,hH⟩:= rideE hh' hM hx ht hζ he k; obtain ⟨d,hd,hD⟩:= nextK hh' hM hx ht hζ (l+1)
    have hr := ruby Q P R hh (fun _=>Λ) s _ _ _ (fun _=> Real.exp 1+1) w hs (Rate.const _) hB hw ((ht.ponies hM).above (by linarith : τ+ξ≤ 2*(τ+ξ*2))) hH hh' (Rate.const _) (by positivity) hq' hy hξ hd (show 1≤l+1+2 by omega) hp N (σ:=σ) (C:=C) (K:=K)
    filter_upwards [hr,cons hO V coat clip w Λ ξ,Delay.shift_pos su L,hD,halfBill v ‹τ<v› hq' hq, ((edge su L).mul hA.ruled).below (by norm_num [vow]) 1 zero_lt_one] with t ht h1 hx hp' h' h2 m' L' M' u c b S F Y k eQ eK e Ω β hC hJ ρ hρ hN Φ hT hG hg X hY hv
    have hS:= h1 c b S F Y k eQ eK hC e hJ ρ hρ
    have hr c (hc:‖c‖<u): Brush (l+1+2) m' 1 (Lapis.orbit F ρ) c:= (hS.curve c hc).smaller (by omega)
    have hK :=crispX Φ hr hS.pos hS.small (by unfold Lapis.orbit Uniform.station; simp [hρ.critical.1]) (fan_pos ..).le hT hG ((le_abs_self _).trans h2) hg h' (Fare.gS β hN.positive).1 hY.habit.2.1 hp'
    refine ht c b S F Y k ρ _ _ β Ω _ X eK eQ ?_ hC hN hO hρ (e.symm ▸ hJ) hY hS ?_ hv
    · subst K; subst Q; subst clip; rfl
    simpa only [abs_of_nonneg (by positivity : 0≤Real.exp 1+1)] using! hK
end YM.QCD.Oasis
#print axioms YM.QCD.Oasis.litE
