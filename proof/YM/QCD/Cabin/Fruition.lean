import YM.QCD.Cabin.Era
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ ψ t:ℝ} {U V:SunR Ω} (P₀:Plan j)
open WilsonStartup.Start WilsonStartup.Padded Progress.DirectedRecipe Ovens
variable (c:Side)(O:Clip)(β:ℝ)(P:BudgetPoint)(N)
lemma deeperT (hc : Decent O P) (h : Loan P ε σ κ b)(hβ : ε ≤ β)(i : ℕ)(U:Grid c): |(payload O P su c β).forced i U| ≤ (Real.exp κ ^ (Start.inventory c i).card)⁻¹ *Start.cash c P σ i := by
  have hb:= cash_pos (b:=P) (σ:=σ) (n:=c) i; dsimp only [payload]; split
  next hi=>
    unfold paid; split
    next had=>
      rw [Start.cash,if_pos hi,Start.offer,if_pos had.1,← Real.exp_nat_mul,← Real.exp_neg,← Real.exp_add,abs_of_pos (Real.exp_pos _),Real.exp_le_exp];
      let D := Start.inventory c i
      have he : D ⊆ flags P.threshold U := by change (name (Start.Foot c) i).val.2⊆_; rw [← had.2]; exact Finset.inter_subset_right
      have hp := charge_price O P hc U D he; have hz:= h.slope; have hh' := mul_le_mul_of_nonneg_left h.allows (by positivity : (0:ℝ)≤ D.card); have hl:= mul_le_mul hβ hp (mul_nonneg (by positivity) (gain_pos _).le) (hz.trans hβ)
      change _ ≤ -(D.card*κ)+ -σ*(D.card:ℝ); nlinarith only [hh',hl]
    simp only [abs_zero]; positivity
  change |(0:ℝ)| ≤ _; simp only [abs_zero]; positivity
lemma trimV (hc:Decent O P)(h: Loan P ε σ κ b)(hβ:ε≤β)(hv:0<t)(hw:w ≤ P.supportExponent+1)(ht:0 ≤ψ)(hg:ψ≤ Real.exp κ): Quits (cueG O P β c N) P.B 1 ψ w t:=by
    let p:= Start.inventory c; let g i:= (Real.exp κ ^ (p i).card)⁻¹*Start.cash c P σ i
    have hm:= h.packets; let Θ':= Real.exp b-1
    have hΘ:0 ≤ Θ':=sub_nonneg.mpr (Real.one_le_exp hm.gamma)
    have hh': Θ' ≤ 1:= (le_mul_of_one_le_left hΘ (one_le_pow₀ (by simp))).trans h.margin
    refine ⟨⟨g,(fun i=>budget_loosen ?_ hh'),?_⟩⟩
    · let Q₀:=cueG O P β c N; apply budget_mono (hm.hit i) (fun j=> ?_) (fun j=>?_)
      · split; next h=> exact mul_nonneg (mul_nonneg (pow_nonneg ht _) (mul_nonneg (by change 0 ≤ (Real.exp κ ^ (p j).card)⁻¹; positivity) (cash_pos _))) (Real.exp_pos _).le -- shape
        next _=> exact le_rfl
      split; next hX=>
          rw [if_pos (show i∈ extent c j from hX)]; apply mul_le_mul ?_ (Real.exp_monotone (mul_le_mul_of_nonneg_right hw (by positivity))) (Real.exp_pos _).le (cash_pos _)
          let x:=Real.exp κ; have hX₁:0 < g j∨ 0=g j:= lt_or_eq_of_le (mul_nonneg (show 0 ≤ (Real.exp κ^(p j).card)⁻¹ from (by positivity)) (cash_pos _)); apply le_trans (show ψ^(p j).card*g j≤ x^(p j).card*g j from mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht hg _) (le_of_lt_or_eq hX₁)) ?_; exact (mul_inv_cancel_left₀ (show x^(p j).card ≠0 from pow_ne_zero _ (Real.exp_ne_zero _)) _).le -- orientation of mul_inv
      next _=>exact (hm.hit i).1 _
    intro i U; apply le_trans (b:=Sen (0:Site c) t (baker c N ((payload O P su c β).forced i U))) (Stew.shot (Stew.lens 0) _ _ hv); rw [vine _ _ _ hv.le]; exact deeperT c O β P hc h hβ i U
lemma terra (hp:Decent O P)(ht:0<t)(hx:P.threshold≤ Start.threshold su P.order P.power)(hy:‖β‖≤ v)(he:Start.book su P v ≤ w): Licence P P.supportExponent w t (cueP O P β c N):=by
    let T:= cueP O P β c N; let Z:=payload O P su c β; have hh:=royal c β O P hp
    obtain ⟨g,hg,h⟩:= Start.ink (G:=su) (n:=c) hx hp.direct hy he
    refine ⟨g,(fun i=>?_ ),fun i=> Reggae.wealthy N _ _ _ (hh.regular.smooth i) (hg i) ht.le⟩
    have hx:=h i; simp only [BudgetPoint.mass, mul_comm (Real.exp _)] at hx; exact hx
noncomputable def birthV (c:Side)(P: BudgetPoint)(N:ℕ)(O:Clip)(b:ℝ): Voice c N:=⟨_,_,cueP O P b c N,cueG O P b c N⟩
lemma payline (q:Flavor N)(hp:Decent O P)(hl: Loan P ε σ κ b)(hy:ε ≤ β)(hw: 1 ≤ P.supportExponent+1)(hq:taxK L x 1≤ Real.exp κ)(hx:P.threshold ≤ Start.threshold su P.order P.power)(hv:‖β‖ ≤ v)(hi:Start.book su P v≤ Jets.Touch.chip L x) : Pencil L P q t x 1 (birthV c P N O β):=by
     let g:= cueP O P β c N; let T:= cueG O P β c N; let f:= fan L t x
     have hr:= fan_pos L t x; have hb:=royal c β O P hp; have hpm:=terra N c O β P hp hr hx hv hi -- `N` binder var param
     have hm:=trimV N c O β P hp hl hy hr hw (Real.exp_pos _|>.le) hq
     obtain ⟨hL,hK⟩:= succeeds N c β O P hp
     exact ⟨⟨visa _ _ hb,hK,shipX q _ _,ready_rose _ _ hb,hL,hpm,hm,fun U=>⟨permits g hpm hr P.exponent_pos.le U,(cashing N c β O P U).summable⟩, zero_lt_one⟩⟩
end Rails
end YM.QCD.Acre
