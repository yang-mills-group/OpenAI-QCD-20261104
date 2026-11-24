import YM.QCD.Finch.Emer
/-! # calibr obtains pivotal mass from THE unmasked book.Any Anchor.T.arb. bootstrap. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f L :Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove Entr YM.Next.Free Bloch Laurent QCD.Free
open Garden Para Pine
variable {t s τ u :ℝ}{j k:ℕ}{B:BudgetPoint}
lemma market (σ:Side→Train j)(Q:Plan j): Tendsto (fun i: Side=> flagW (wood Q (0:Site i) (σ i) 1)) atTop (𝓝 0):=by
    let f(i:Side)(x:Momentum):= model (Dir (σ i) x) chad chad
    have hz:Moderate (fun _:Side =>1) f:=(coil (Dir_budget Q.good σ) false).tap chad chad
    have ht:= bring f hz id; have hh (i:Side): flagW (wood Q (0:Site i) (σ i) 1)= (f i (zerov i)).re:=by
       unfold flagW; rw [bare_this,unbarred,carries]; apply congr_arg; exact if_pos rfl
    apply ((Complex.continuous_re.continuousAt.tendsto.comp ht)).congr; intro x; rw [hh]; change (f x _-f x _).re=_; rw [show f x 0=0 from ?_,sub_zero]
    unfold f; rw [Dir_nil,show model 0=0 from map_zero Para.signal]; rfl
lemma roller (P:I→ Side→ Prop)(S:Side)(hp:∀ f:Side→I,∀ᶠ i:Side in atTop,P (f i) i):∀ᶠ i in atTop,∀ j,P j i:=by
    by_cases h: Nonempty I
    · have hh i:∃ x:I,(P x i→ ∀ j,P j i):=by
         by_cases he:∀ j,P j i; · exact ⟨Classical.choice h,fun _=> he⟩
         push Not at he; obtain ⟨j,hj⟩:=he; exact ⟨j,fun h=>(hj h).elim⟩
      choose f hf using hh; exact (hp f).mono fun i h=> hf i h
    exact Eventually.of_forall fun i j=> (h ⟨j⟩).elim
lemma earnings (P:Plan j)(hp:0<t)(hz:4≤j) (h:4≤k) (L:Side):∀ᶠ c:Side in atTop, (∀ Z:Train j,|flagW (wood P (0:Site c) Z 1)| ≤ t) ∧ ∀ (G:Flight j k), G.L=L →∀ (f: Side) (e:f.val=c.val*G.L.val), |flagW (Garden.barP G e *proton G e)- (L.val:ℝ)|≤ t:=by
     have ht:∀ᶠ i:Side in atTop,∀ v:cocoa L j k, |(Quixote v.val (zerov i) chad chad).re-(L.val:ℝ)|≤ t:=by
        refine roller _ 1 fun f=>?_ ; let F(i:Side):=(Quixote (f i).val (zerov i) chad chad).re
        have he:Tendsto F atTop (𝓝 (L.val:ℝ)) :=by convert (Complex.continuous_re.continuousAt.tendsto.comp (spin f (fun i=>(f i).prop) hz h)) using 1; rfl; simp
        filter_upwards [Metric.tendsto_nhds.mp he t hp] with n hn; exact (Real.dist_eq ..).symm.trans_le hn.le
     have hx:∀ᶠ i:Side in atTop,∀ Z:Train j, |flagW (wood P (0:Site i) Z 1)|≤t:=by
        refine roller _ 1 fun v=>?_ ; filter_upwards [Metric.tendsto_nhds.mp (market v P) t hp] with i hi; exact (by rw [Real.dist_eq,sub_zero] at hi; exact hi.le)
     filter_upwards [ht,hx] with c hh hv; refine ⟨hv,fun G he f e=>?_⟩; unfold flagW; rw [rockP G e P]; refine le_trans (le_of_eq (show _= |(Quixote G (zerov c) chad chad).re-(L.val:ℝ)| from ?_)) (hh ⟨G,he⟩)
     congr 3; exact if_pos rfl
lemma projecting (hp:0<t)(h:4≤j)(hz:4≤k)(P:Plan j)(T:Plan k)(L:Side)(K A:ℝ)(ha:0<A):∀ᶠ c: Side in atTop, ∀ (B:BudgetPoint), fare A B.B*K ≤ c.val*(t/2) → ∀ (I:Type) [Fintype I],∀ (S:Gem c N I)(a:Flavor N)(w:ℝ),0<w→Crossing S → Licence B A (K*w^2) w S →
     (∀ v:Train j, (∑ i,S.view i 1)=Port.paleF N (wood P 0 v 1) → |qMass (till S a 0)|≤t)∧∀ (f:Side) (G:Flight j k)(e:f.val=c.val*G.L.val), G.L=L→(∑ i,S.view i 1)=Port.paleF N (Garden.barP G e*proton G e)→ |qMass (till S a 0)-(L.val:ℝ)|≤t:=by
     filter_upwards [earnings P (half_pos hp) h hz L] with c hr; intro B hK I _ S a w h' ht he
     let p:= qMass (till S a 0); have h (M:Sheet c)(h:(∑ i,S.view i 1)=Port.paleF N M): |flagW M-p| ≤ t/2:=le_of_mul_le_mul_left ((fareM S a he ha _ h h' ht).trans hK) (by positivity : 0<(c.val:ℝ))
     refine ⟨fun v hv=> ?_,fun f G e hx hv=>?_ ⟩
     · obtain ⟨h0,h1⟩:=abs_le.mp (h _ hv); obtain ⟨h2,h3⟩:= abs_le.mp (hr.1 v); unfold p at *; apply abs_le.mpr; constructor<;>linarith
     obtain ⟨h0,h1⟩:=abs_le.mp (h _ hv); obtain ⟨h2,h3⟩:=abs_le.mp (hr.2 G hx f e); unfold p at *; exact abs_le.mpr ⟨by linarith,by linarith⟩
end YM.QCD.Finch
