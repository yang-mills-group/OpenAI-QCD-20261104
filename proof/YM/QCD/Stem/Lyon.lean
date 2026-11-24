import YM.QCD.Stem.Mag
import YM.QCD.Coda.Vent
/-! # High expenses from the exact catalogue cut. `Silence` words allowed. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Moss
open QCD Lat PhysicalNext.Repeat
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {c f C F L₀ : Side} {P : Patch} {M D' n: ℕ} {K : Teller su}
variable {p a b W U V t d r g : ℝ}
open Loom Fleet Patron Cove GasP Grove Stew King
local notation "B'"=> radiusB p
section scrap
variable {I:Type}{E:Gem c n I}{B:BudgetPoint}
noncomputable def muteK (E:Gem c n I)(P:I→ Prop): Gem c n I:=⟨E.addr,fun i V=> if P i then E.view i V else 0⟩
-- restrict high complement
lemma stencil (f:I→ℝ)(S:I→Support c)(g:ℝ)(X:ℕ→I→Prop)(hf:Ac.Hit S n f t d)(hx:∀ i,∀ᶠ k in atTop,¬X k i)(hg:0<g): ∀ᶠ k in atTop, Ac.Hit S n (fun i=> if X k i then f i else 0) t g:=by
   refine eventually_all.mpr fun x=>?_ ; have hv:=hf x; let u i := if x∈S i then f i*Real.exp (t*coverNumber n (S i)) else 0; let w k i:= if X k i then u i else 0; have hu : SumBudget u d:= hv
   have H k i: 0≤ w k i :=by unfold w; split; exact hu.1 i; rfl
   have ht k i:w k i ≤u i:=by unfold w; split; rfl; exact hu.1 i
   have hx' i:Tendsto (fun k=>w k i) atTop (𝓝 0):= tendsto_const_nhds.congr' ((hx i).mono fun k hk=> (if_neg hk).symm)
   have hh:= tendsto_tsum_of_dominated_convergence hu.2.1 hx' (Eventually.of_forall (fun k i=> (show ‖w k i‖≤ u i from (by rw [Real.norm_of_nonneg (H k i)]; exact ht k i))))
   rw [tsum_zero] at hh; filter_upwards [hh.eventually_le_const hg] with k hk
   have hz: SumBudget (w k) g:= ⟨H k,hu.2.1.of_nonneg_of_le (H k) (ht k),hk⟩
   convert hz using 2 with i; unfold w u; split<;> split <;> simp_all
lemma eitherX (E:Gem c n I)(X:I→Prop)(i:I): (muteK E X).view i= if X i then E.view i else 0:=by
    split
    next he=> exact funext fun _=> if_pos he
    next he=> exact funext fun _=>if_neg he
lemma freeK (o:Site c)(X:Support c): Woven o X B t (0:Grid c→EvenA c n) 0:=by
    convert Woven.sumX (v:=fun _:ℕ=> 0) (c:=c) (a:=t) (p:=B) (o:=o) (B:=X) (N:=n) ∅ (fun i=>0) (by simp) <;> simp -- t name
lemma hitL (f z:I→ℝ)(X:I→Support c)(hp:Ac.Hit X n f a d)(hv:∀ i,0 ≤ z i)(hr:∀ i,z i ≤f i) : Ac.Hit X n z a d:= by
    refine fun x=>budget_mono (hp x) (fun i=>?_) fun i=>?_ --edit
    · split; exact mul_nonneg (hv _) (Real.exp_pos _).le; exact le_rfl
    split; exact mul_le_mul_of_nonneg_right (hr i) (Real.exp_pos _).le; exact le_rfl
lemma joined (f z:I→ℝ)(X:I→Support c)(hp: Ac.Hit X n f a g)(hv: Ac.Hit X n z a d): Ac.Hit X n (f+z) a (g+d):=by
    intro x; convert budget_plus (hp x) (hv x) using 2 with i; dsimp only [Pi.add_apply]; split<;>ring
lemma raisins (X:I→Prop)(Y:ℕ→I→ Prop)(Q:ℕ→I→ Prop)(f:I→ℝ)(hb:∀ i,Woven (E.addr i).site (E.addr i).support B t (E.view i) (f i))(hv:∀ i,E.view i ≠0→∀ k,Y k i → X i ∨ Q k i)(hQ:∀ i,∀ᶠ k in atTop, ¬ Q k i)(hr:0<r) (ha:Ac.Hit (fun i=>(E.addr i).support) D' f a g)(hp:Ac.Hit (fun i=>(E.addr i).support) D' (fun i=>if X i then f i else 0) a d): ∀ᶠ k in atTop, ∃ f:I→ℝ, (∀ i,Woven (E.addr i).site (E.addr i).support B t ((muteK E (Y k)).view i) (f i)) ∧ Ac.Hit (fun i=>(E.addr i).support) D' f a (d+r):=by
    filter_upwards [stencil f _ r Q ha hQ hr] with k hk; let z i:= if X i then f i else 0; let w i:=if Q k i then f i else 0; have hz i: 0≤z i:=by unfold z; split; exact (hb _).travel; rfl
    have hx i: 0≤w i:=by unfold w; split; exact (hb _).travel; rfl
    refine ⟨z+w,fun i=>?_,joined z w _ hp hk⟩
    rw [eitherX]; split
    next he=> by_cases hh:E.view i=0
              · rw [hh]; exact (freeK ..).stretches (Subset.refl _) (add_nonneg (hz _) (hx _))
              rcases hv i hh k he with h|h
              · refine (hb _).stretches (Subset.refl _) ?_; unfold z; rw [Pi.add_apply,if_pos h]; exact le_add_of_nonneg_right (hx _)
              refine (hb _).stretches (Subset.refl _) ?_; unfold w; rw [Pi.add_apply,if_pos h]; exact le_add_of_nonneg_left (hz _)
    next h=> exact (freeK ..).stretches (Subset.refl _) (add_nonneg (hz _) (hx _))
end scrap
-- survivors. remove Aliased cases all even if in catalog; disjoint by branch
open QCD.Beam QCD.Port
variable {S:StepData c f}{R:BudgetPoint}{T:Tube su S} {X: ConnectedActivityE6.Target su K} {o:ConnectedActivityE6.Target.Order su W}{β δ:ℝ}{D: Cash W p a L₀ X o U T (trimP T R δ β b)}
variable {I:Type}{N:ℕ}
open Blaze King Silica Patron Sands Leaf Tee Orbit Garden Jets Flume Run YM.Next.Free
variable {B:Fleet D I N}{u v:ℕ}{O:Flight u v}{h:f.val=c.val*O.L.val}{A J μ γ C':ℝ}{π : St f}{U₀:ℕ→Atom su 2} {P':Plan v}
variable {L: Swathe O h π U₀ P' A J μ γ C' M}{Γ:Land c (Site c) (Site c)}
set_option quotPrecheck false
local notation "G"=>tiro B L Γ
local notation "S₀"=>artV B L Γ
variable {A₀:Clusters (S₀).Bright →RegularAddress c}{V₀:Chi}
local notation "T₀"=> crude (S₀) V₀ A₀
-- nonE pick

def ExtraK (B:Fleet D I N)(L : Swathe O h π U₀ P' A J μ γ C' M)(Γ:Land c (Site c) (Site c))(p:Clusters (artV B L Γ).Bright):Prop:=∃ q:(artV B L Γ).Bright,∃ i:I,p= individual q ∧ Aliased (artV B L Γ) q (.inl i)
set_option maxHeartbeats 600000 in
lemma bornLate {Z:Fleet D (I⊕ Varn f c⊕ Gaze c) N}{G':Bouquet D Z}{A:Clusters Z.Bright→RegularAddress c}{Q':BudgetPoint}(hr:0<r)(hz:Gosh Z V₀ g t Q'.order Q'.power)(hB:Q'.B=radiusB p)(hq:Q'.threshold=Pressure.temp p)(hA:∀ i,(A i).support=seatP Z.lightF i) {Qk:ℕ→Clusters Z.Bright→Prop}
  (hK:∀ i,(crude Z V₀ A).view i≠0→∀ k,Qk k i→ Dated Z Fury nectarP p i ∨ i∉ dashX k G' ∧ ∃ j:Wreath c f, ∃ W:Mossy D j,i=G'.heightV j W):∀ᶠ k in atTop, ∃ F, (∀ i,Woven (A i).site (A i).support Q' t ((muteK (crude Z V₀ A) (Qk k)).view i) (F i)) ∧ Ac.Hit (seatP Z.lightF) Q'.B F g (jelly L₀ p+r):=by
    let E:= fun k i=> i∉ dashX k G' ∧ ∃ j:Wreath c f, ∃ W:Mossy D j,i=G'.heightV j W
    have hh i:∀ᶠ k in atTop, ¬ E k i:=by
        by_cases h:∃ j:Wreath c f,∃ W:Mossy D j,i=G'.heightV j W; · obtain ⟨j,h,rfl⟩:=h; exact (lateM D j h).mono fun k hk e=> e.1 ((oceanM ..).mpr ⟨j,h,((leads ..).1 hk).2,rfl⟩)
        filter_upwards with k using (fun hz=> h hz.2)
    obtain ⟨z,hx,hz',hv⟩ :=hz.bills
    have he := hx Q' A hA rfl rfl hB hq; simp_rw [← hA] at he
    let W':=fun i=>(A i).support; have ht : seatP Z.lightF=W':= funext fun i=>(hA i).symm
    let X i:= Dated Z Fury nectarP p i
    rw [ht] at hz' hv; rw [ht,hB]; exact raisins (E:=crude Z V₀ A) X Qk E z he hK hh hr hz' hv
end YM.QCD.Moss
