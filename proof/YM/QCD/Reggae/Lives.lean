import YM.QCD.Reggae.Oc
import YM.QCD.Simple
/-! # Scalar tune on actual pressure irrespective of gas. Can leave elementary mass shift to separate bank. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Reggae
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{p:BudgetPoint}{z u a r t w:ℝ}{i j x:Site c}
open WilsonStartup Port AnalyticBridge.VerifiedReset Collection Extra.Iteration Footprint Progress.DirectedRecipe Ovens Averaging Geo
variable {ι:Type}[Countable ι](E:Gem c N ι)(b:Flavor N){P:PathData su}{α β δ σ C Λ ε:ℝ}{v:Clip}
set_option quotPrecheck false
local notation "Δ"=> Averaging.delta ((theater E).read (stock E))
local notation "X"=> shelves (theater E) P p
local notation "Y"=> fill (theater E) P v p (stock E) α (Δ)
local notation "Z"=> ostinato (X) (Y) N
lemma taxes (h:Crossing E)(hp:Licence p (Quotes.preExponent p) u a E)(ht:0 < a)(hq:P.Bounds v σ C Λ)(hc:Decent v p)(hw: Geo.Width p v σ)(hn:20 < c.val) : Licence p p.supportExponent (regularNeed su p v σ C α u) a (Z) ∧ Purchases (riff (X) (Y) N) p.threshold p.B (p.supportExponent+1) (softNeed su p v σ C α u) a ∧ ∀ U, HasSum (fun i=> (riff (X) (Y) N).mean i U) (baker c N (∑' i,(Y).logarithm i U)) :=by
    let W:= Z; let V:= regularNeed su p v σ C α u; let x:= X; let y:= Y; let P':=theater E; let q:=stock E
    have he:=regMoney E h hp ht.le; let f:= riff x y N; have hk' : Payments.Fittings y x p:= he.fittings simple hq hc hn α (Δ)
    obtain ⟨g,hg,hB⟩:=he.cheap; let M:= numbering (EKey c); let D:= numbering (LKey c); let u' := quoteE (n:=c) P p v α (Δ) g; let r':=quoteL (n:=c) P p v α (Δ) g; obtain ⟨hr,hL⟩:= Local.quote_family hq hc hw α (Δ) hg hB (delta_bound simple he.projects)
    have hr₁ i: p.supBounds (W.addr i).site (W.addr i).support (y.regular i) (u' (M i)) := Local.quote_regular simple hq hc α (Δ) hg he.smooth (M i)
    have hr₂ : Licence p p.supportExponent V a W:=by
       refine ⟨u' ∘ M,fun i=>?_,fun i=> wealthy N _ _ (y.regular i) (hk'.regular.smooth i) (hr₁ i) ht.le⟩
       have hR : Anchored (fun k=> (W.addr k).site) (u' ∘ M) (fun k=> coverNumber p.B (W.addr k).support) p.supportExponent V:=by
           intro j; let L i:=incoming P' P p i; have hb: SumBudget (fun i=> if (L (M i)).site=j then p.mass (L (M i)).support (u' (M i)) else 0) V:= Extra.Iteration.Cost.equiv M (hr j)
           simpa only [BudgetPoint.mass, W, x,L,P',ostinato,shelves,M,u',Function.comp_apply,mul_comm (Real.exp _)] using hb -- x var clash binder
       exact hR i
    have hx i U : ‖y.logarithm i U‖≤ r' (D i):= Local.quote_soft simple α (Δ) hg he.smooth (D i) U
    obtain ⟨hf,hF⟩:=readySoft x y hk' (N:=N); let d:=softNeed su p v σ C α u; have he': Ac.Hit f.bud p.B (r' ∘ D) (p.supportExponent+1) d:=fun i=>Extra.Iteration.Cost.equiv D (hL i)
    refine ⟨hr₂,⟨hF,hf,r' ∘ D,?_,he'⟩,fun U=> visor x y U hx he'⟩; intro i U; apply le_trans (b:=Sen (0:Site c) a (baker c N (y.logarithm i U))) (shot (lens 0) _ _ ht); rw [vine 0 _ _ ht.le]; exact hx _ _
-- compare normalized exponent. budget priorm
noncomputable def pulse (P:PathData su)(v:Clip)(p:BudgetPoint)(β τ:ℝ)(U:Grid c): ℝ:= τ*(Fintype.card (Site c)) - P.inChannels v p β U
lemma tune (h:Crossing E)(hp:Licence p (Quotes.preExponent p) u a E)(ht:0 < a)(hq: P.Bounds v σ C Λ)(hc: Decent v p)(hw:Geo.Width p v σ)(hn:20<c.val)(hv:Quanta E b):
    let δ:=Δ; let x:=X; let y:=Y; let A:=weave (wade E) (Z)
    Quartz A ∧ Quanta A b ∧ Crossing A ∧ Licence p p.supportExponent (2*u+regularNeed su p v σ C α u) a A ∧ Purchases (riff x y N) p.threshold p.B (p.supportExponent+1) (softNeed su p v σ C α u) a ∧ p.threshold^2*|δ| ≤ u ∧∀ (U:Grid c)(β τ:ℝ),
       HasSum (fun i=>(riff x y N).mean i U) (baker c N (pulse P v p β τ U- α*receipt P v p U)+Patron.total E p.threshold U- (baker c N (pulse P v p (β+α+δ) (vac (stock E) τ) U)+Patron.total A p.threshold U)):=by
    intro δ x y A
    have hσ:=p.exponent_pos; have hσ' : p.supportExponent ≤ Quotes.preExponent p:= by unfold Quotes.preExponent; linarith
    have he:= regMoney E h hp ht.le; obtain ⟨hV,hQ,hR⟩:=taxes E h hp ht hq hc hw hn (α:=α); have hh:Payments.Fittings y x p:=he.fittings simple hq hc hn α _
    have hE: Licence p p.supportExponent (2*u) a (wade E):= passes E h hp ht.le hσ'; obtain ⟨h1,h2⟩:=pilots E h
    refine ⟨quip _ _ h1 (ready_rose _ _ hh), fibs _ _ b (fiber E b hv) (shipX b x y),pilot _ _ h2 (visa _ _ hh),guardL _ _ hE hV,hQ,delta_bound simple he.projects,?_⟩
    intro U β τ; have he' :=permitShape U ht hσ hσ' hp; have hw0:= medlar E U he'; let S:= Z; let W:= Patr E U p
    let d:=((theater E).read (stock E)).additive p U; let B:=pulse P v p β τ U - α*receipt P v p U; let B':=pulse P v p (β+α+δ) (vac (stock E) τ) U; let k:=(x.pours y).additive p U; have hv := he.exponent simple hq hc hw α hn β τ U; have h₀:(∑' i,y.logarithm i U)=(B-d)-(B'-k):=by
       change B'-k + (∑' i,y.logarithm i U)= (pulse P v p β τ U-d) - α*receipt P v p U at hv; unfold B; linarith only [hv]
    have hb0:=permits _ hV ht hσ.le U
    have hh': HasSum (fun i=> (riff x y N).mean i U) (baker c N (∑' i,y.logarithm i U)):=hR U
    rw [h₀,map_sub,map_sub,map_sub] at hh'; unfold A; rw [woven_sum (wade E) (Z) U (permits _ hE ht hσ.le U) hb0,perms E U he',rose_sum x y U hb0,octave,hw0,ocean]; simp only [ContinuousLinearMap.neg_apply]
    rw [map_sub] at hh'; rw [map_sub]; unfold d k B' at hh'; abel_nf at hh' ⊢; exact hh'
where
  permitShape U (ht:0<a)(hσ:0<p.supportExponent) (hs:p.supportExponent ≤ Quotes.preExponent p)(hp:Licence p (Quotes.preExponent p) u a E): Summable (letters E p.threshold U):=permits E hp ht (hσ.le.trans hs) U
  Patr (q: Gem c N ι) V (p:BudgetPoint):= Patron.total q p.threshold V
end YM.QCD.Reggae
