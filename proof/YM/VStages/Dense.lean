import YM.MassiveQCD.Charter.Lane
import YM.MassiveQCD.Apron.Suppert
import YM.MassiveQCD.Apron.Card
import YM.Massive.Beacon.Spark
import YM.QCD.Calm.Current
import YM.Massive.Commerce.Plain
/-!
 Extends Apertures at different patch orders (NB original uses high.J semantically only when same).
# a genuine raw step with varying-flavor capability

Use `QCD.Loom.chartered`, Calm::Current with only the warp and no other gauge
projection hypotheses: the analytic radius will not require the integrands
to be real throughout, and the desired masses break flavor symmetry. Retain
the same loop scope on unmarked spin/gauge data. `Gosh`'s second estimate
retains the special `jelly` strength at `Dated` entries.

Also return the original `PortD` condition when the full `Pant` holds for
these inputs. Therefore this same step can be used for the earlier common
shooting. This result alone prices the step in *broad* E norms and offers
no iteration capability yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {P:Teller su}(Q:Target su P) -- edit
variable {N m l i j k:ℕ}{C A D η p h z a b t v u u' q θ:ℝ}
variable (P₁:Plan j)(P₂:Plan k)
open Blaze King March GasP Ursell Stew Patron
open Shells Sands

/-! `Pew`: after shape choice, late payment. Same cash for tagged marks at *any prescribed order* on enough-money stages. No higher order assumption on the Tube needed here beyond patch overlap. -/
def Pew (s:Side)(W μ:ℝ)(D:RG.Patch)(o:Target.Order su W)(C a b t q U A h v u η α r z σ D' Y B ηP aP:ℝ)(iP p p' Jq Kq:ℕ)(χ:Chi)(N:ℕ)(x:ℝ):Prop :=
    let δ:=lowK s x P.top.supportExponent; let Z:=highW s v h x; let g:=coneK s r x
    ∀ (E:Garden.Offer 1 a q)(E': Garden.Offer 2 b U)(X:ℕ→Atom su 2),Extra.Iteration.Charged X t A → Extra.Iteration.SymmetricAtoms X → ∀ (c f: Side)(G:Flight j k)(H:f.val=c.val*G.L.val)(K:KernelChoices)(R:BudgetPoint) (m β w:ℝ) (T:Tube su (Flight.visit G K H)), G.L=s→ (G.visit K H).patch=D →2*(radiusB x+1)< f.val→ SliceRows.Stamp T → R.threshold =fiery su x s → betaF su x s/2 ≤β→|m|≤ wink s x→
    let T':=park G H P₁ E E' (haloK s x) m
    ∀ p₀ : Cash W x μ G.L Q o C T (trimP T R δ β w),Seats p₀ χ ∧ Nonempty (Jets.Sun G c f H g z σ η D' p (park G H P₁ E E' (haloK s x) 0)) ∧ (Works P s x (Flight.visit G K H) T → T.up.Bounds T.high P.top.width P.top.paths (loopBill su s x) → β≤2* betaF su x s →∀ I : BudgetPoint,I.supportExponent=P.top.supportExponent → I.B=highR s x → I.threshold=fiery su x s → Nonempty (Cash W x μ G.L Q o C T (Sands.lore (trimP T I δ β w)))) ∧∀ (G₁:Sun G c f H g z σ η D' p T') (V':Swathe G H T' X P₂ z g η Y B p'), Bay.Sacred G₁→ ∀ (Γ: Land c (Site c) (Site c)) (Yv:Pays c (Site c) (Site c)), Run.Pack id id ηP ((Q.relative*(10*preCost 37)+3)+1) iP (wood P₂ 0 G.land) aP Γ Yv → Villa.Torch Γ →∀ {E J:Type}[Countable E][Countable J] (f': Rise f N E J),∀ (w:E→ℝ) (g:J→ℝ), Cents f' w g (fan s h x) R.threshold → Fill f' w g u u (taxK s x 1) 1 (chip s x) (highR s x) → f'.Wave R.threshold→ f'.Reframe → ∀ (X:Type)[Fintype X](μ':X→Bool)(T₂: MassiveQCD.Stitch.Tablet f' X)(ψ:X→Site f), T₂.Wave R.threshold μ' ψ→ T₂.Coins w g (fan s h x) R.threshold→ MassiveQCD.Apron.Grove.Supplies G H K p₀ G₁ V' Γ T₂ ψ Z χ μ' α h Jq Kq
open MassiveQCD.Apron (vantage)
set_option maxHeartbeats 1400000 in
theorem flexMarch (ηP aP:ℝ)(iP:ℕ)(hr₁:0<ηP)(ha₁:0<aP)(α:ℝ)(hq:Q.rate ≤ -(3/8:ℝ))(Jq Kq:ℕ)(χ:Chi)(hα:0≤α)(hQe:α+1+1≤Q.exp) (hP:4≤j)(hQ:4≤k)(N:ℕ)(h η v u:ℝ)(hx:0<h)(hz:h<1/8)(hr:0<η)(he:0<u)(ht:1≤v): ∃ n:ℕ,∀ s:Side,n ≤ s.val → ∀ᶠ W in atTop, 0<W ∧ ∃ μ:ℝ,0< μ ∧∀ D:RG.Patch, D.Branches P.bind su → D.L=s→ D.J=j → ∃ (o:Target.Order su W)(C:ℝ), ∀ (a b t q U A:ℝ),0<a→0<b→0<t→0≤q→0≤U→
   ∃ (r z σ D' Y B:ℝ)(p p':ℕ), 0<r ∧ (∀ Jq' Kq':ℕ,∀ᶠ x in atTop,Pew Q P₁ P₂ s W μ D o C a b t q U A h v (u/2) η α r z σ D' Y B ηP aP iP p p' Jq' Kq' χ N x) ∧∀ᶠ x:ℝ in atTop,
    let δ:=lowK s x P.top.supportExponent; let Z:=highW s v h x; let g:=coneK s r x
    0<δ ∧ ∀ (E:Garden.Offer 1 a q)(E': Garden.Offer 2 b U)(X:ℕ→Atom su 2),Extra.Iteration.Charged X t A → Extra.Iteration.SymmetricAtoms X → ∀ (c f: Side)(G:Flight j k)(H:f.val=c.val*G.L.val)(K:KernelChoices)(R:BudgetPoint) (m β w:ℝ) (T:Tube su (Flight.visit G K H)), G.L=s→ (G.visit K H).patch=D →2*(radiusB x+1)< f.val→ Works P s x (Flight.visit G K H) T → SliceRows.Stamp T → R.threshold =fiery su x s → R.B=highR s x →R.supportExponent=P.top.supportExponent →T.up.Bounds T.high P.top.width P.top.paths (loopBill su s x) → betaF su x s/2 ≤β→β≤2* betaF su x s→|m|≤ wink s x→
    let T':=park G H P₁ E E' (haloK s x) m
    Nonempty {V:Jets.Sun G c f H g z σ η D' p T' // Bay.Sacred V} ∧ Nonempty (Swathe G H T' X P₂ z g η Y B p') ∧ Nonempty (Cash W x μ G.L Q o C T (PhysicalNext.Repeat.Pane.virgin T R β)) ∧ ∃ p₀ : Cash W x μ G.L Q o C T (trimP T R δ β w), Nonempty (Cash W x μ G.L Q o C T (Sands.lore (trimP T R δ β w))) ∧∀ (G₁:Sun G c f H g z σ η D' p T') (V':Swathe G H T' X P₂ z g η Y B p'), Bay.Sacred G₁→ ∀ (Γ: Land c (Site c) (Site c)) (Yv:Pays c (Site c) (Site c)), Run.Pack id id ηP ((Q.relative*(10*preCost 37)+3)+1) iP (wood P₂ 0 G.land) aP Γ Yv → Villa.Torch Γ →∀ {E J:Type}[Countable E][Countable J] (f': Rise f N E J),∀ (w:E→ℝ) (g:J→ℝ), Cents f' w g (fan s h x) R.threshold → Fill f' w g u u (taxK s x 1) 1 (chip s x) (highR s x) → f'.Wave R.threshold→ f'.Reframe → Villa.PortSparse G K H p₀ G₁ V' f' Γ h Z α ∧ (Villa.Pant f N R.threshold f' → Villa.PortD G K H p₀ G₁ V' f' Γ h Z α) ∧ let Z₁:= tableau G H K f' p₀ G₁ V' Γ; Seats p₀ χ ∧ Gosh Z₁ χ α Z Jq Kq :=by -- edit
  have he' : 0≤Q.relative:=by unfold Target.relative; have he:= Q.usable; have hQ:=Q.pos; linarith [Q.bound]
  obtain ⟨n,hn⟩:= dilation P₁ P₂ N 38 36 (u/2) Q.relative v h η Q.relative hx hP hQ hz he' he' (by linarith) hr (by linarith)
  obtain ⟨m,hM⟩:=Q.issue
  let γ:= η/2; let gq:=γ/4; have hv₁:0<γ:=half_pos hr; have hq₀ : 0 < gq := by unfold gq; positivity
  obtain ⟨l',hl⟩:=Fees.exponent 36 hq₀ he' (show 2*gq<γ from by unfold gq; linarith)
  obtain ⟨l'',hM'⟩:=King.air P Q
  obtain ⟨uv,wx,hA⟩:= Eider.weave su
  obtain ⟨Z',hZ',hΩ'⟩:= March.oar su Jq
  obtain ⟨omeg,hN⟩:= Oboe.ell P Q
  refine ⟨l'' +l'+n+m+omeg,fun L hL=>?_⟩ -- rename
  filter_upwards [hM L (by omega)] with W hW
  refine ⟨hW.1,?_⟩; obtain ⟨μ,hm,hk⟩:= hW.2
  refine ⟨μ,hm,fun D he' hhD hR=>?_⟩
  obtain ⟨o,C,hC,hp⟩:= hk D he'; refine ⟨o,C,fun a b t q Ω Y ha hb ht hu hΩ=>?_⟩
  obtain ⟨A,RB,X,i₁,B,x,y,p,q,hX⟩:=hn L (by omega) a b q Ω t Y ha hb hu hΩ ht
  refine ⟨x,y,p,q,X,RB,i₁,B,hX.grow.orbit,?_ ,?_⟩ -- R'/X swap
  · intro Jv Kv
    obtain ⟨Z',hZ',hΩ'⟩:= March.oar su Jv
    let t i:=2*Pressure.fiery su i L
    let t₀ i:=(Jv+1:ℝ)*Z'*t i; have hv₂: Rate su L (-(1/2)) t₀:=((Rate.flame (L:=L)).mul_left 2).mul_left ((Jv+1:ℝ)*Z')
    have hm₁ : ∀ᶠ i in atTop, 0 < t i:= (Delay.shift_pos su L).mono fun x hh=> mul_pos (by norm_num) (Work.E09.temp_pos hh)
    have hh : ∀ᶠ i in atTop,0 < t₀ i:= hm₁.mono fun i hi=> by unfold t₀; positivity
    obtain ⟨g,Ω₁,U,Zq,F,K₁,K₂,C₁,hz₁,hg,hΩ,hu₁,hV',hf,hz'⟩:=hM' L (by omega) D he' χ Jv μ W hW.1 hm o uv wx hA t₀ hv₂ (hh.mono fun _ h=>h.le)
    obtain ⟨A₁,Q',B₁,E₁,M₃,_,hX0⟩:= hN L (by omega) D he' Jv χ W hW.1 μ hm o uv wx (by assumption) t₀ hv₂ (hh.mono fun _ h=>h.le)
    have ht₁ (c f:Side)(p:Ratio c f)(h:p.count=L): Footprint.reserve γ Q.relative (Footprint.conversion p 36) gq:=hl _ _ p (h.symm ▸ (show l'≤ L.val from by omega))
    filter_upwards [summer_ext hX hx hz ‹1≤v› 0 C μ W hm hC o t₀ hv₂ γ hv₁ (by unfold γ; linarith) gq ht₁ χ Jv ηP aP iP hr₁ ha₁, hp,Work.E01.radiusB_tendsto.eventually_ge_atTop 1, dipK L P.top.supportExponent,(Work.E09.betaF_growth su L).eventually (eventually_gt_atTop 1), Fleet.afterK (Q:=Q) L μ _ hm hx hα hQe, hX.permit,hz',hm₁,hh, King.given L Q hm hz₁ h α hx hq Jv (2*Jv+K₂) (2+Kv*Jv) hα hQe _ (takeStock U F Ω₁ Zq L Jv hu₁ hf hΩ hV'),hX0] with τ hi hZ hv hu hz hC' hV hM ht₀ hp₀ hD hX0
    unfold Pew; intro δ X' g
    intro V V' R hr' hv' c f G H K I b' β w T he hT hn ht' hϑ hb' hn' D₁
    obtain ⟨hg,hF,hp'⟩:= hi c f G H K T he hn V V' b' R hn' hr' hv'
    have hS: (G.visit K H).patch.L=L:=he
    let T':= trimP T I δ β w
    intro l'; refine ⟨?_,?_,?_,?_⟩
    · clear hhD hS; subst L; obtain ⟨Ξ,hΨ,hXh⟩:= hM _ _ (G.visit K H) _ hT ht' (trimP T I δ β w) _ l'; obtain ⟨W',hw0⟩:= hX0 _ _ (G.visit K H) T hT ht' (trimP T I δ β w) C l'; exact ⟨_,_,_,_,_,_,_,_,_,W',hw0,hp₀⟩
    · exact (hi c f G H K T he hn V V' 0 R (by simpa only [abs_zero] using (abs_nonneg _).trans hn') hr' hv').1
    · intro hP₀ hT₀ hΩ I₀ h₀ hL₀ hϑ₀
      have ht₀ : Intake P T τ (trimP T I₀ δ β w):= climate τ T I₀ w (hS ▸ hϑ₀) h₀.symm hP₀.funds (hS ▸ hz) (hS ▸ hL₀) (hS ▸ And.intro hb' hΩ) (hS ▸ hT₀) (by rw [h₀,hS]; exact hu.2.1)
      have Hv:= ConnectedActivityE6.circulates ((hZ _ _ (G.visit K H) _ hT hP₀).2 (Sands.lore (trimP T I₀ δ β w)) (Sands.chips _ ht₀) ht')
      rw [he]; exact Hv
    intro Z v₀ HH Γ Yv hYv hpΓ
    intro J E _ _ R₀ dV dX hf hZc hw hp
    have h1(F: Tree.Forest (G.visit K H).ratio):=_root_.id (hp' Z v₀ I β w l' Γ Yv hYv hpΓ R₀ dV dX (hϑ ▸ hf) hZc (hϑ ▸ hw) hp F)
    obtain ⟨Y,η',v₁,v₂,j,hw',hj,⟨hU,hU'⟩,hXx⟩:=h1 (Classical.choice (Tree.select (G.visit K H).ratio G.odd))
    have hP (hp:Villa.Pant f N I.threshold R₀):= Villa.irisA G K H l' Z v₀ R₀ hp HH hw hpΓ hU.2.2 hw' hj
    have hPor:Villa.PortC G K H l' Z v₀ R₀ Γ h X' α:=by
      obtain ⟨heco,hcor⟩:= Villa.iris_color G K H l' Z v₀ R₀ hp hw hU.2.2 hw' hj
      apply Villa.dew_colored G K H l' Z v₀ R₀ _ heco hP hcor hv (mul_pos (by linarith : 0 < v) (fan_pos ..)) -- castle
      · simpa only [he] using hC' (Loom.shiftCost L τ (Loom.romp L)) C β -- h implicit o? check
      intro F; obtain ⟨Y',η₁,v₃,v₄,k',hη,hj',⟨hF',_⟩,_⟩:=h1 F; exact ray G H K R₀ l' Z v₀ Γ F hη hF' hw hu.1 hj' hv
  
     
    clear hhD hS
    subst L
    obtain ⟨Ξ,hΨ,hXh⟩:= hM _ _ (G.visit K H) _ hT ht' (trimP T I δ β w) _ l'
    intro I' hI' tq R hpZ Hw hsB
    let Xq:=vantage G H K l' Z v₀ Γ R hpZ X'
    have ht' := hϑ ▸ hsB -- equality? hϑ : I.threshold=..., term.Elab req
    obtain ⟨he₁,r0,hc1,hf₀,hv0,hg1,hg2⟩:= hXx I' tq R hpZ Hw ht'
    obtain ⟨hc0,hc2⟩:= MassiveQCD.Apron.Grove.accustomed G H K l' Z v₀ Γ R hpZ X' Hw hPor.color hPor.wordsP hv
    have hd:0 < δ:=hu.1; refine ⟨⟨hf₀,?_,hv0,hc1,hc2,hc0,?_⟩,?_,Hw,he₁,r0,hd,hv⟩
    · intro F; obtain ⟨_,_,_,_,_,_,_,_,hp⟩:=h1 F; exact (hp I' tq R hpZ Hw ht').2.2.2.2.2.1
    · exact hC' (Loom.shiftCost G.L τ (Loom.romp G.L)) C β
    obtain ⟨x,hx,hV₀⟩:= hg2 _ _ _ _ _ _ _ _ _ _ Ξ hΨ hp₀.le
    let C₀:=δCharge G.L h τ
    have hM :=hD β hb'
    have hx₀ : 0 < lushR Jv (U τ) (Ω₁ τ) (royal (F τ)) (Zq τ):=by
       unfold lushR
       have he:= hΨ.extra; have hv :1≤ Ω₁ τ:=Ξ.active; have hf:= hx.alive
       positivity
    have hz:1 ≤ betaF su τ G.L:= (show 1 < betaF su τ G.L from hz).le
    have hT:= strengths Xq Ξ hXh hz (fun i=> (paintCost i hz).1) hx.cost hV₀ hM.hood hM hx₀ Fury nectarP (fun i=> (paintCost i hz).2.2) (fun i=> (paintCost i hz).2.1)
    refine ⟨_,?_,hT⟩
    let s:= tableau G H K R₀ l' Z v₀ Γ; let κT:= hPor.meta G K H l' Z v₀ R₀ hv
    intro p A hA iQ iV hB hm i; have hp: p.threshold≤t τ:=by rw [hm]; exact l'.laws.data.room.temperatures
    have hh:Sailor su p.threshold (Z'*t τ) Jv:=⟨fun c x h=> hΩ' c _ ht₀.le x (h.trans hp)⟩
    have hv : Jv*(Z'*t τ)≤ t₀ τ :=by unfold t₀; nlinarith
    have he:0 < X':= mul_pos (zero_lt_one.trans_le (by assumption)) (fan_pos ..)
    have hg:= King.gold_colored Xq Ξ hΨ hx hf₀ hc0 A ⟨hc1⟩ hA i iQ hp₀ he hh hm (mul_pos hZ' ht₀).le hv C₀ hc2
      (fun E _ _ _ V x h=> MassiveQCD.Apron.Grove.essences G H K l' Z v₀ Γ R hpZ X' hf₀ h (Villa.grassZ G K H l' Z v₀ R₀ κT.1 hU.2.2 hw' h))
    rw [iV,hB] at hg; exact hg
  let t i:=2*Pressure.fiery su i L
  let t₀ i:=(Jq+1:ℝ)*Z'*t i; have hv₂: Rate su L (-(1/2)) t₀:=((Rate.flame (L:=L)).mul_left 2).mul_left ((Jq+1:ℝ)*Z')
  have hm₁ : ∀ᶠ i in atTop, 0 < t i:= (Delay.shift_pos su L).mono fun x hh=> mul_pos (by norm_num) (Work.E09.temp_pos hh)
  have hh : ∀ᶠ i in atTop,0 < t₀ i:= hm₁.mono fun i hi=> by unfold t₀; positivity
  obtain ⟨g,Ω₁,U,Zq,F,K₁,K₂,C₁,hz₁,hg,hΩ,hu₁,hV',hf,hz'⟩:=hM' L (by omega) D he' χ Jq μ W hW.1 hm o uv wx hA t₀ hv₂ (hh.mono fun _ h=>h.le)
  obtain ⟨A₁,Q',B₁,E₁,M₃,_,hX0⟩:= hN L (by omega) D he' Jq χ W hW.1 μ hm o uv wx (by assumption) t₀ hv₂ (hh.mono fun _ h=>h.le)
  have ht₁ (c f:Side)(p:Ratio c f)(h:p.count=L): Footprint.reserve γ Q.relative (Footprint.conversion p 36) gq:=hl _ _ p (h.symm ▸ (show l'≤ L.val from by omega))
  filter_upwards [budgetK hX hx hz ‹1≤v› 0 C μ W hm hC o t₀ hv₂ γ hv₁ (by unfold γ; linarith) gq ht₁ χ Jq ηP aP iP hr₁ ha₁, hp,Work.E01.radiusB_tendsto.eventually_ge_atTop 1, dipK L P.top.supportExponent,(Work.E09.betaF_growth su L).eventually (eventually_gt_atTop 1), Fleet.afterK (Q:=Q) L μ _ hm hx hα hQe, hX.permit,hz',hm₁,hh, King.given L Q hm hz₁ h α hx hq Jq (2*Jq+K₂) (2+Kq*Jq) hα hQe _ (takeStock U F Ω₁ Zq L Jq hu₁ hf hΩ hV'),hX0] with τ hi hZ hv hu hz hC' hV hM ht₀ hp₀ hD hX0
  intro δ X' g
  refine ⟨hu.1,?_⟩; intro V V' R hr' hv' c f G H K I b' β w T he hT hn hP' ht' hϑ hA hh hu' hb' hx' hn' D₁
  obtain ⟨hg,hF,hp'⟩:= hi c f G H K T he hn V V' b' R hn' hr' hv'
  have hS: (G.visit K H).patch.L=L:=he
  let T':= trimP T I δ β w
  have ht : Intake P T τ T':= climate τ T I w (hS ▸ hϑ) hh.symm hP'.funds (hS ▸ hz) (hS ▸ hA) (hS ▸ And.intro hb' hx') (hS ▸ hu') (by rw [hh,hS]; exact hu.2.1)
  obtain ⟨l⟩:= ConnectedActivityE6.circulates ((hZ _ _ (G.visit K H) _ hT hP').2 T' ht ht'); have hm:Nonempty (Cash W τ μ G.L Q o C T T'):=by rw [he]; exact ⟨l⟩
  obtain ⟨l'⟩:=hm
  have h1:= hV f c hn G H he V V' b' hn'; -- portal allows
  obtain ⟨Xs,Hs⟩:= inverse_spine G H h1.2.2.1 (Classical.choice hg)
  refine ⟨⟨Xs,Hs⟩,hF,?born,l',?non,fun Z v₀ HH Γ Yv hYv hpΓ=>?_⟩
  case born=>
     have hd:= PhysicalNext.Repeat.Pane.whey f su I
     have hv : Intake P T τ (PhysicalNext.Repeat.Pane.virgin T I β):= ⟨hP'.funds, ⟨rfl,rfl,hS ▸ hϑ⟩, ⟨(hS ▸ hu'), { hd with boundE:=AnalyticBridge.VerifiedReset.Time.E_rises hd.boundE (by unfold incomingE; positivity), boundK:=AnalyticBridge.VerifiedReset.Time.K_rises hd.boundK (Real.exp_pos _).le }⟩,hh.symm,hS ▸ hz,hS ▸ hA,hS ▸ And.intro hb' hx' ⟩
     have hv:=ConnectedActivityE6.circulates ((hZ _ _ (G.visit K H) _ hT hP').2 _ hv ht'); rw [he]; exact hv
  case non => have H₂:= ConnectedActivityE6.circulates ((hZ _ _ (G.visit K H) _ hT hP').2 (Sands.lore T') (Sands.chips T' ht) ht'); change Nonempty (Cash W τ μ G.L Q o C T (Sands.lore T')); rw [he]; exact H₂
  intro J E _ _ R₀ dV dX hf hZc hw hp
  have h1(F: Tree.Forest (G.visit K H).ratio):=_root_.id (hp' Z v₀ I β w l' Γ Yv hYv hpΓ R₀ dV dX (hϑ ▸ hf) (Acre.fillF hf hZc (by linarith only [show 0 < u from (by assumption)]) (by linarith only [show 0 < u from (by assumption)])) (hϑ ▸ hw) hp F)
  obtain ⟨Y,η',v₁,v₂,j,hw',hj,hU,hU'⟩:=h1 (Classical.choice (Tree.select (G.visit K H).ratio G.odd))
  have hP:= Villa.iris_frame G K H l' Z v₀ R₀ hp hw hU.2.2 hw' hj
  have hPor:Villa.PortSparse G K H l' Z v₀ R₀ Γ h X' α:=by
    apply Villa.dew_frame G K H l' Z v₀ R₀ _ hP.1 hP.2 hv (mul_pos (by linarith : 0 < v) (fan_pos ..)) -- castle
    · simpa only [he] using hC' (Loom.shiftCost L τ (Loom.romp L)) C β -- h implicit o? check
    intro F; obtain ⟨Y',η₁,v₃,v₄,k',hη,hj',hF',_⟩:=h1 F; exact ray G H K R₀ l' Z v₀ Γ F hη hF' hw hu.1 hj' hv

   
  refine ⟨hPor,fun hx=> Villa.PortSparse.dress _ _ _ _ _ _ _ hPor (Villa.irisA G K H l' Z v₀ R₀ hx HH hw hpΓ hU.2.2 hw' hj),?_⟩; intro Y'
  -- substitute L? all hv etc with
  clear hhD hS
  subst L
  obtain ⟨Ξ,hΨ,hXh⟩:= hM _ _ (G.visit K H) _ hT ht' (trimP T I δ β w) _ l'
  obtain ⟨W',hw0⟩:= hX0 _ _ (G.visit K H) T hT ht' (trimP T I δ β w) C l'
  refine ⟨⟨_,_,_,_,_,_,_,_,_,W',hw0,hp₀⟩,?_⟩
  obtain ⟨x,hx,hV₀⟩:= hU' _ _ _ _ _ _ _ _ _ _ Ξ hΨ hp₀.le
  let C₀:=δCharge G.L h τ
  have hM :=hD β hb'
  have hx₀ : 0 < lushR Jq (U τ) (Ω₁ τ) (royal (F τ)) (Zq τ):=by
     unfold lushR
     have he:= hΨ.extra; have hv :1≤ Ω₁ τ:=Ξ.active; have hf:= hx.alive
     positivity
  have hz:1 ≤ betaF su τ G.L:= (show 1 < betaF su τ G.L from hz).le
  have hT:= strengths Y' Ξ hXh hz (fun i=> (paintCost i hz).1) hx.cost hV₀ hM.hood hM hx₀ Fury nectarP (fun i=> (paintCost i hz).2.2) (fun i=> (paintCost i hz).2.1)
  refine ⟨_,?_,hT⟩
  let s:= tableau G H K R₀ l' Z v₀ Γ; let f₀ : Tree.Forest (G.visit K H).ratio:=Classical.choice (Tree.select (G.visit K H).ratio G.odd)
  intro p A hA iQ iV hB hm i; have hp: p.threshold≤t τ:=by rw [hm]; exact l'.laws.data.room.temperatures
  have hh:Sailor su p.threshold (Z'*t τ) Jq:=⟨fun c x h=> hΩ' c _ ht₀.le x (h.trans hp)⟩
  have hv : Jq*(Z'*t τ)≤ t₀ τ :=by unfold t₀; nlinarith
  have he:0 < X':= mul_pos (zero_lt_one.trans_le (by assumption)) (fan_pos ..)
  have hg:= King.gold_frame Y' Ξ hΨ hx (hPor.within f₀).1 hPor.speak A ⟨(hPor.within f₀).2.1⟩ hA i iQ hp₀ he hh hm (mul_pos hZ' ht₀).le hv C₀ hPor.warp
    (fun E _ _ _ V x h=>Villa.grassZ G K H l' Z v₀ R₀ (hPor.within f₀).1 hU.2.2 hw' h)
  rw [iV,hB] at hg; exact hg
end YM.QCD.Loom
#print axioms YM.QCD.Loom.flexMarch
