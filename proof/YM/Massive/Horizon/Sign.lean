import YM.QCD.Purse.Sign
import YM.Massive.Horizon.Bank
import YM.Massive.Horizon.Tower
/-! Step width and price of the principal regular output under the collar/grade3 condition. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Shells
open ConnectedActivityE6 ConnectedActivityE6.Blaze Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side}{j n l k : ℕ} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {O R : BudgetPoint} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B t t' w y u: ℝ}
variable {δ β B₀:ℝ}{Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T (trimP T R δ β B₀)}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Spice Lat Multi Multi.Puff Kit Jets Port Fork Sands Fj
variable {N':Libretto su j}
-- Hue bridge ANY δ.Surface.Mat. No wind.G.In when bads.
variable {E J:Type}[Countable E][Countable J] {d':Ratio c f}
variable (G₁:Rise f N E J)
open Flume YM.Next.Free Stew Leaf Jets.Touch Jets.Sun -- inspect
variable {L':Flight n k}{G: f.val=c.val * L'.L.val}{T':Run.St f}
open Garden Run Leaf Tee Orbit Quarry Pine
variable {f₀ KQ Ω zp e r' :ℝ}{P₀': Plan n}{F₁:Offer 1 f₀ KQ}{F₂: Offer 2 Ω zp}
variable (P₀:Sun L' c f G t u q r a l (pesto P₀' L' G (trunkM F₁ F₂ e r' f)))(P':Sun L' c f G t u q r a l (pesto P₀' L' G (trunkM F₁ F₂ e 0 f)))(s':Finset (Fj (Tr f) E J)) (K :ℕ)
local notation "κ"=> radiusB s
variable {u':ι}(h : Tone Y (P₀.equip N (radiusB s)) G₁ s' u')
local notation "Z"=> lore (trimP T R δ β B₀)
variable (F':Cash W s μ L Q o C T (lore (trimP T R δ β B₀))) -- L conflict delete
variable (hX: ((lore (trimP T R δ β B₀)).activities.reg K).support=brimW (P₀.equip N (radiusB s)) G₁ s')
variable {ξ x y' T₁ τ z w0 φ:ℝ}
local notation "L₁"=> P₀.equip N (radiusB s)
variable (i:E)(ht:leftE s'={i}) (hI:((lore (trimP T R δ β B₀)).activities.reg K).site=(G₁.row i).site)
variable (Z₁: Hera.Rights su j) (D:Heir.Record) (hP:Plays N' D O R P T s)
-- Ψ geometry in 2 earnings: hemiH post price. `Γ.boot` before δ LL calibration
variable (g:ℝ) (hp: Peak (P₀.equip N (radiusB s)) R.threshold x y ξ fun i=> Real.exp 1*terra P₀ N (radiusB s) x y i)(hr:0 ≤ r)(hF:G₁.Wave R.threshold)(hw:y*fingers N*q ≤ ξ*x)(hq:∀ i,terra P₀ N (radiusB s) x y i≤1)
variable (hΔ:Sea L' G (radiusB s) t φ q R.threshold P₀.Z P₀.V 2)(hl:4*((fingers N*φ)*y)≤x/4) -- halo
variable {m m':ℕ}{a₀ :ℝ}
local notation "X"=> coreW (P₀.equip N (radiusB s)) G₁ s'
-- halo bill at here oANY
set_option quotPrecheck false
open Dust Brick
-- Fleck only needs Pot.Walk extent.Grow.Wrapped.
lemma phores3 {U V:Support f}{o:Site f}{f':Grid f→EvenA f N}(i: Bool)(h:Fleck R U o i f' x y)(hp:U⊆V): Fleck R V o i f' x y:=by
   refine {h with wine:= h.wine.stretches hp le_rfl, base:= ?_}
   obtain ⟨he,hq,hb⟩:=h.base; exact ⟨AnalyticBridge.CouplingShape.reg_extend he hp,hp hq,hb⟩
include h hX ht hI hP
local notation "A'"=> Brim.plate F' K
local notation "o'"=> (G₁.row i).site
local notation "S'"=> S.ratio
local notation "Zx"=> (Z).activities.reg K
-- Caller independent.N threshold. epsilon.C angular beam. prices before Shooting.
variable (hy:coverNumber (radiusB s) (Brim.plate F' K).support ≤radiusB s) (hβ:0≤z)(hk:z<t/2)(hv:0 < w)(hq':fareG 1 w N ≤ y)
variable {ζ ψ ψ' K0 V U z₀ θ M₀ M γ α :ℝ}
local notation "Z₁'"=> (loom O (Heir.reach s) N'.C)
variable (hw':Warp L'.L (G₁.row i).site ((sliceL L' G).parent (G₁.row i).site) (ply L' G) N x y ψ ψ') (hδ:4*(a₀*y)≤V*(x/4)) (hs:4*((fingers N*φ+a₀)*y)≤x/4) (hV:0 ≤ V) (hφ:0≤φ) (hC:0≤a₀) (hK:fingers N* Spice.soil P₀' L'.L (radiusB s) l r t z ζ q |r'| a 2 ≤ a₀)
variable (hS:∀ n:ℕ,(1+(n:ℝ))^2 ≤ ζ*Real.exp (r/2*n))(hζ:0≤ζ)(hE:0< r)(hn:5≤j)(f4: Bool) (hA:Nonwrapping (G₁.row i).support (G₁.row i).site→ Fleck R (G₁.row i).support (G₁.row i).site f4 (G₁.main i) x τ) (hO:Short S R (brimW (P₀.equip N (radiusB s)) G₁ s')) (hi:ops s'=∅) (hR:G₁.Reframe)
variable (ε A0 Q0:ℝ)(hψ:∀ x:su.Color, ‖x‖≤ ε→su.chord (su.lieExp x)≤ A0*‖x‖)(hw₁:0≤ A0)
-- Ξ.photos x positive threshold.Number. actor.Teller
variable (hMQ:N'.M*loom O (Heir.reach s) N'.C ≤1) (hM:tender Z₁ 1 (N'.M * loom O (Heir.reach s) N'.C) ≤ fern S.patch.L^(furl f4)) (hwM:N'.M*loom O (Heir.reach s) N'.C ≤ ε) (hwN:D.Q*loom O (Heir.reach s) N'.C≤ ε)
variable (hQX:∀ (U V:Grid f)(p:Support f)(t:ℝ), BeamRaw p U V t→beamAt p U V (Q0*t)) (hA':Q0*g + Q0*(A0*loom O (Heir.reach s) N'.C*(D.Q+N'.M+N'.M)) ≤ z)
include χ hp hF hE hδ hs hV hΔ hq' hR hw' hφ hC hK hS hζ hn hA hO hMQ hM hwM hwN hQX hψ hi hA' hw₁ hβ hk hv hy P'
set_option maxHeartbeats 450000 in
theorem sonnet3 : let d:=Malachite.radiusD s; Lore Y O N' F' χ D g u' K τ ((1+(d:ℝ))^2*(Real.exp τ*τ^2)+V*τ) (carryFee N' Z₁ ψ'*τ *fern L'.L^(furl f4)) w:=by
    intro d; constructor; intro F y0 X' K' hv' ht' hV' v p hQ
    let P'':=mapcase F' K F; have hn':1 ≤ j:=by omega
    obtain ⟨q,hg⟩:= P''.canvas p.site (Finset.subset_union_left p.anchor) hV' hP.space N'.Z hn' hP.rehearsed.wire -- primed Z C from mapcase.Heir.area. check lemma
    let g' := q ∘ S.ratio.parent
    have htP:p.site=o':=hI
    have hsP:S.patch.L=L'.L:=congr_arg Ratio.count h.born
    have hwX:Warp S.patch.L p.site ((S').parent p.site) (ply L' G) N x y ψ ψ':=by rw [htP,hsP,show S'= _ from h.born]; exact hw'
    let U:= (G₁.row i).support
    have hT:Short S R p.support:=hX.symm ▸ hO
    have hh:U⊆ p.support:= hX.symm ▸ (Subset.trans (leafSub P₀ G₁ s' _ ht) (native_sub L₁ G₁ s'))
    have hq:0<gStep β := inv_pos.mpr (Real.sqrt_pos.mpr (F'.laws.intake.positive))
    have hm:Nonwrapping p.support p.site:= short_nonwrap hT hP.rehearsed.weft.cover hP.space p.anchor
    have hb:= hA (fun i hi=>by rw [← htP]; exact hm i (hh hi))
    have he: rootBill ((sliceL L' G).parent o') w K':=by rw [← h.born,← htP]; exact ht'
    have hqg:g'=q ∘ (sliceL L' G).parent:=congr_arg (fun L:Ratio c f=> q ∘ L.parent) h.born
    have hw₁': BeamRaw (brimW (P₀.equip N κ) G₁ s') (Lattice.gauge g' v) 1 (A0* Z₁'*(D.Q+N'.M+N'.M)):= by
        have ht'':= printing (k:=y0) (q:=χ) (d:=0) (ε:=ε) P'' hP hg hT hn' p.anchor (1:Grid f) hq.le hψ hw₁ hwN hwM -- K
        exact hX ▸ ht''
    let Zp:=skimR (q ∘ (sliceL L' G).parent) (testG q K') (proton L' G) (G₁.main i)
    have hp' i' (hi: Healthy R.threshold (brimW (P₀.equip N κ) G₁ s') i'):= authored G₁ R s' i P₀ hp ht hb.wine w K' he q i' hw' hi hq' hv
    obtain ⟨hx,hf,hg'⟩:= hp' v (hX ▸ hQ)
    refine ⟨Zp,hX.symm ▸ hx,hf,(fun U h=>(hp' U (hX ▸ h)).2.2),?_,?_⟩
    · intro Z' hU HX
      rw [h.cash]; apply lineage G₁ R s' i P₀ P' hp hF ht h.stops hi hR hb.wine q w K' he (f':=φ) hΔ (aboard Y G₁ P₀ s' K h F' hX i hI hy) hK hδ hC hV hs hv hq' Z' (hX ▸ hU) _ hk hS hβ hE hζ hφ
      rw [← hqg]
      have hV:=raysFort _ _ _ (hQX _ _ _ g (celia _ _ _ (hX ▸ HX) g')) (hQX _ _ _ _ hw₁')
      exact fun i a b=> (hV i a b).trans hA' 
    have ht : Fleck R p.support p.site f4 (G₁.main i) x τ:= htP.symm ▸ phores3 f4 hb hh
    unfold Horn;
    have he':= Dust.flowers3 y0 χ 0 Z₁ P'' hP hg hT hn p.anchor hV' (1:Grid f) hq.le _ hwX (testG q K') (kinFare _ hv _ q ht' hq') ht (guard_silent χ hq (mul_pos D.guards R.threshold_pos)) hMQ hM (Q.halo+5)
    have hF:Zp = skimR (q ∘ S.ratio.parent) (testG q K') (proton L' G) (G₁.main i):=congr_arg (fun g=> skimR g (testG q K') (proton L' G) (G₁.main i)) hqg.symm
    rw [hF,← hsP]; exact he'
end YM.QCD.Shells
namespace YM.QCD.Shells
open ConnectedActivityE6 ConnectedActivityE6.Blaze Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side}{j n l k : ℕ} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {O R : BudgetPoint} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B t t' w y u: ℝ}
variable {δ β B₀:ℝ}{Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T (trimP T R δ β B₀)}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Spice Lat Multi Multi.Puff Kit Jets Port Fork Sands Fj
variable {N':Libretto su j}
open Garden Stew Dust Brick YM.Next.Free Jets.Touch Orbit Further Leaf Tee Flume Quarry Pine
open Planned.AtomRegular
open Run Jets Jets.Sun
-- field-economies agile any H supportExponent; τ positive. Bulk/Rush in later ledger. This snapshot number.D. allows auxiliary quantities. E use G.F.
variable {E J: Type}[Countable E][Countable J]{d0 N₂ W₂ :ℕ}
variable {G:Flight n k}{H':f.val=c.val*G.L.val} (G₁:Rise f N E J) {i:Finset (Fj (Tr f) E J)} {a₀ a₁ b₀ b₁ m ξ g w' θ K α φ: ℝ}
variable {P₀ : Plan n}{T₁: Garden.Offer 1 a₀ a₁}{T₂: Garden.Offer 2 b₀ b₁}
variable (Y₀: Jets.Sun G c f H' t' u q η a d0 (pesto P₀ G H' (trunkM T₁ T₂ w m f)))
variable (Y': Jets.Sun G c f H' t' u q η a d0 (pesto P₀ G H' (trunkM T₁ T₂ w 0 f)))
variable {i':ι}{D:Heir.Record} (U: Cash W s μ L Q o C T (lore (trimP T R δ β B₀)))
local notation "ζ"=> radiusB s
set_option quotPrecheck false
local notation "Gz"=> Y₀.equip N (radiusB s)
variable {z p' α' τ ψ' χ₀ ρ x X Y₁:ℝ}
variable (Z: Hera.Rights su j)
variable (hL:Works P L s S T)(hO:O.B=radiusB s)(he:News P L s W Q o μ C j N' D χ O.power z p' g S.patch) (hp:Plays N' D O R P T s)
variable (Ω:Clusters Y.Bright → RegularAddress c)
variable (f':Bool) (β':E→ℝ)(κ:J→ℝ)
local notation "Jz"=> Lute.Plented N' D O R L (Q.halo+5) s (gStep β)
local notation "μ₀"=> fun i=>Real.exp 1*terra Y₀ N ζ x y i
local notation "ψ₁"=> cashM L θ s
variable {f'' : Flavor N}{ρ₀ e e' ψ σ α₂ Y₂ :ℝ}{p: Y.Bright}
variable (hy: Tone Y (Y₀.equip N (radiusB s)) G₁ i i')
variable (hh:Coins O R P L D Q.halo N' Z s β x y t' u η σ q a u z g ρ m p' ξ x θ P₀ N d0)
variable (hm:|m| ≤haloK L s)(ha: Peak (Y₀.equip N (radiusB s)) R.threshold x y ξ fun i=>Real.exp 1*terra Y₀ N (radiusB s) x y i)(hk:Sea G H' (radiusB s) t' φ q R.threshold Y₀.Z Y₀.V 2)(hK:0 ≤ φ)(hj:4*(fingers N*φ*y) ≤ x/8)(hu:y*fingers N*q ≤ ξ*x)(hQ:∀ i,terra Y₀ N (radiusB s) x y i ≤1)
variable (hf:G₁.Wave R.threshold) (hC:G₁.Reframe)(hr:0<η)
variable (hs:Seats H χ)(hP:Aliased Y p i') (hZ:Y.Famous)(hΨ:Stained.Framed Y)
variable (l':ℕ) (ht:α≤ y)(hz:0<α)(h'h:fareG 1 α N ≤ y)
local notation "U₀"=> ((lore (trimP T R δ β B₀)).activities.reg l')
local notation "A₀"=> Brim.plate U l'
variable (hU:( (lore (trimP T R δ β B₀)).activities.reg l').support=brimW (Y₀.equip N (radiusB s)) G₁ i)(hδ:coverNumber O.B (Brim.plate U l').support ≤ O.B)
local notation "A₁"=> ((crude Y χ Ω).view (individual p))
variable (hV: Woven (Brim.plate U l').site (Y.fullA p.val) O α ((crude Y χ Ω).view (individual p)) Y₂)
-- pricing principal. no Height test from Obr.Record eventually.
variable (e0:E)(hX:leftE i={e0})(hW:((lore (trimP T R δ β B₀)).activities.reg l').site=(G₁.row e0).site) (hG: Spice.Worth G₁ e0 R x τ) (hτ: τ ≤ chip L s)
local notation "M₀"=> G₁.row e0
local notation "n₀"=> coverNumber R.B (brimW (Y₀.equip N ζ) G₁ i)
include hL hO hp he hm ha hk hK hy hu hQ hj hf hΨ hr hs hP hZ hh hU hδ hV ht hz hX hW hG hτ
set_option maxHeartbeats 650000 in
lemma param_fairT (hm':ops i=∅)(hj':5≤j)(hΓ:Warp G.L (G₁.row e0).site ((sliceL G H').parent (G₁.row e0).site) (ply G H') N x y ψ ψ')(hI:Nonwrapping (M₀).support (M₀).site→Fleck R (M₀).support (M₀).site f' (G₁.main e0) x τ)(hx:fareG 1 α N≤y)(hh': G₁.Reframe)(Y': Jets.Sun G c f H' t' u q η a d0 (pesto P₀ G H' (trunkM T₁ T₂ w 0 f))): Woven (A₀).site (A₀).support O α A₁ (fern L^(furl f')*τ*fluteT N' Z O ψ' n₀):=by
    let n' := n₀; let f₀:= fern L^(furl f'); let X:=(U₀).support; have hxB:coverNumber R.B X=n':=congr_arg (coverNumber R.B) hU
    have hS : S.patch.L = L:= H.laws.data.funds.length_eq; have hD: G.L=L:= (congr_arg Ratio.count hy.born).symm.trans hS
    obtain ⟨ε,V,Q',ζ₀,ρ',hε,hR,hρ,hN,hMQ,hF,hB',hQ',hz',he',hρ',hA,hB,hρV,hG',hv,hN',hX'⟩:= hh.law.purse
    have hθ:=hO ▸ hδ; have ht:R.B ≤ 2*radiusB s:= hh.harp
    let r' x := Hera.lyreFee N' x D O R L X (Q.halo+5) s (gStep β); let H₀:=hh.planet
    have hb:0≤gStep β:=by unfold gStep; positivity
    have hΨ'(t)(ht':0≤t): r' t ≤ t*Hera.dueFee N' O n':= Hera.tern H₀ ht hh.hemp hb ht' _ hxB.le
    obtain ⟨f0,f1,v1,w1,w2,w3,w4,w5,w6,Ψ₀,hY,h0⟩:=hs
    have h'a:=hG.travel; obtain ⟨h1,h2⟩:=hh.wood.dawn _ h'a hτ
    have hV2:= alertF N' Z O ψ' n'; have heE := alert N' O n'; let A:=1+(n':ℝ); have hN0:1 ≤ A^15:=one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
    have hV':0 ≤ f₀*τ*fluteT N' Z O ψ' n':=by have he:=hV2.2; positivity [fern_pos L]
    have hB0 := f₀; let y₀:=f₀*τ -- edit have real no type?
    have hD₂: fern L^5 ≤ fern L^(furl f') := pow_le_pow_of_le_one (fern_pos _).le (fern_one L) (by unfold furl;split <;> omega)
    by_cases hz₀ : Heir.Short S R (brimW Gz G₁ i)
    · have hQ0: 4*((fingers N*φ+ρ')*y) ≤ x/4:=by rw [add_mul]; linarith
      have hG: 0 ≤ q:=by obtain ⟨V,hV,hm,hH⟩:=(hk 0).1.stocks; exact (sum_nonneg (fun i _=> hV i)).trans hm
      have H' :=sonnet3 (χ:=χ) Y G₁ Y₀ Y' i l' hy U hU _ hX hW Z D hp g ha hf hk hθ hN' hX' hz hx hΓ hρV hQ0 hv hK hρ' (hD.symm ▸ hB hG Y₀.stable.calf.le m hm) hA he' hr hj' f' hI hz₀ hm' hh' ε V Q' hε hR hMQ (hS.symm ▸ hF.trans hD₂) hN hρ (hB' f) hQ'
      let B:= carryFee N' Z ψ'; have hΨψ := cin N' Z ψ'
      apply fundsF Y hL he hp hO i' l' (grill Y G₁ hy hU) Ω hY h0 hZ hΨ p hP Y₂ hV hδ H' h'a (by positivity) (by positivity [fern_pos G.L]) hV'
      · change _+ r' (B*τ*fern G.L^(furl f')) ≤ _; rw [hD]; have hV₃: B*Hera.dueFee N' O n' ≤ max (carryFee N' Z ψ') (Hera.grandFee Z)*Hera.dueFee N' O n'*A^15:=by
         apply le_trans (b:=B*_*A^15) (le_mul_of_one_le_right (mul_nonneg hΨψ heE) hN0); gcongr; exact le_max_left ..
        apply (add_le_add (h1.trans (mul_le_mul_of_nonneg_right hD₂ h'a)) (hΨ' _ (by positivity [fern_pos L]))).trans; change f₀*τ+(B*τ*f₀)*_ ≤_
        have he : 1+B*Hera.dueFee N' O n' ≤ fluteT N' Z O ψ' n':= (add_le_add (by norm_num : (1:ℝ) ≤2) hV₃).trans hV2.1
        rw [show _+_=f₀*τ*(1+B*Hera.dueFee N' O n') from by ring]; exact mul_le_mul_of_nonneg_left he (by positivity [fern_pos L])
    have hzB: L.val ≤ n'^3:=hS ▸ le_of_not_gt hz₀
    have h'A: 4*(fingers N*φ*y)≤ x/4:= hj.trans (by linarith [ha.bud]); have hf:= islands χ Y G₁ Y₀ i l' hy U hU _ hX hW Z D hp g ha hr.le hf hu hQ hk h'A hθ (fun U V H=> gridBeam _ (hB' f U V _ _ H) hz') hN' hX' hG hz (by assumption)
    dsimp only at hf; simp only [hm',prod_empty,mul_one,if_true, Finset.card_empty,Nat.cast_zero,zero_mul,add_zero] at hf
    let n:ℕ:=(hooks (F:=N) (sliceL G H') (coreW Gz G₁ i)).card; let D':=Hera.grandFee Z; let z0:=σ/(t'/2); have heψ:=sinR Z
    have hξ : 1≤ ξ:=ha.post; have hz' : 0 ≤ z0 :=by unfold z0; positivity [Y₀.positive]
    apply Woven.stretches (A:=_) _ (Subset.refl (A₀).support) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD₂ h'a) (show 0 ≤ fluteT _ _ _ _ _ from (by norm_num : (0:ℝ)≤2).trans hV2.2))
    let f₀:=fern L^5
    let y₀:=f₀*τ
    apply fundsF Y hL he hp hO i' l' (grill Y G₁ hy hU) Ω hY h0 hZ hΨ p hP Y₂ hV hδ hf h'a (by positivity [Y₀.positive]) (mul_nonneg heψ h'a) (show 0≤ f₀*τ*fluteT N' Z O ψ' n₀ from by have h:=hV2.2;positivity [fern_pos L])
    have hf₀: arid s*τ*(τ*Real.exp τ + (n:ℝ)*(ξ*z0))*|z|+τ*|p'| ≤ y₀:=by
       have hx := (h2 n (Nat.cast_nonneg n) (Nat.cast_le.mpr (detailed Y G₁ hy l' hU hθ).2)).1; apply le_trans _ hx; gcongr; apply le_mul_of_one_le_left h'a; exact one_le_pow₀ (by linarith only [show 0≤(Malachite.radiusD s:ℝ) from Nat.cast_nonneg _])
    apply (add_le_add hf₀ (Hera.wide H₀ hh.harp hh.hemp hb (mul_nonneg heψ h'a) n' hxB.le hzB)).trans; change y₀+ D'*τ * _ * _ * f₀≤_
    rw [show y₀+ _ = y₀ * (1+D'*Hera.dueFee N' O n'*A^15) by unfold y₀ n' f₀ D' A; ring] -- check A unfold
    apply mul_le_mul_of_nonneg_left _ (by unfold y₀; positivity [fern_pos L]); apply le_trans _ hV2.1; apply add_le_add (by norm_num : (1:ℝ)≤2); gcongr; exact le_max_right ..
end YM.QCD.Shells
#print axioms YM.QCD.Shells.param_fairT
