import YM.MassiveQCD.Column.Transmission
import YM.QCD.Shell.Ethos

/-! # Pay comparison on the SAME `Lore` hulls. The deterministic comparison spin opens otherwise exactly as in `Shell/Ethos`. This is for actual Tone of a singleton output. -/
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
-- Temper only needs Pot.Walk extent.Grow.Wrapped.
lemma temperatures {U V:Support f}{o:Site f}{f':Grid f→EvenA f N}{g:Bool}(h:Temper R U o g f' x y)(hp:U⊆V): Temper R V o g f' x y:=by
   obtain ⟨hw,hv,hG,hr,he,hx,hz⟩:=h
   exact ⟨hw.stretches hp le_rfl,hv,hG,hr,AnalyticBridge.CouplingShape.reg_extend he hp,hp hx,hz⟩
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
variable (hS:∀ n:ℕ,(1+(n:ℝ))^2 ≤ ζ*Real.exp (r/2*n))(hζ:0≤ζ)(hE:0< r)(hn:5≤j){gain:Bool} (hA:Nonwrapping (G₁.row i).support (G₁.row i).site→ Temper R (G₁.row i).support (G₁.row i).site gain (G₁.main i) x τ) (hO:Short S R (brimW (P₀.equip N (radiusB s)) G₁ s')) (hi:ops s'=∅) (hR:G₁.Reframe)
variable (ε A0 Q0:ℝ)(hψ:∀ x:su.Color, ‖x‖≤ ε→su.chord (su.lieExp x)≤ A0*‖x‖)(hw₁:0≤ A0)
-- Ξ.photos x positive threshold.Number. actor.Teller
variable (hMQ:N'.M*loom O (Heir.reach s) N'.C ≤1) (hM:tender Z₁ 1 (N'.M * loom O (Heir.reach s) N'.C) ≤ fern S.patch.L^5) (hwM:N'.M*loom O (Heir.reach s) N'.C ≤ ε) (hwN:D.Q*loom O (Heir.reach s) N'.C≤ ε)
variable (hQX:∀ (U V:Grid f)(p:Support f)(t:ℝ), BeamRaw p U V t→beamAt p U V (Q0*t)) (hA':Q0*g + Q0*(A0*loom O (Heir.reach s) N'.C*(D.Q+N'.M+N'.M)) ≤ z)
include χ hp hF hE hδ hs hV hΔ hq' hR hw' hφ hC hK hS hζ hn hA hO hMQ hM hwM hwN hQX hψ hi hA' hw₁ hβ hk hv hy P'
set_option maxHeartbeats 450000 in
theorem transmit : let d:=Malachite.radiusD s; Lore Y O N' F' χ D g u' K τ ((1+(d:ℝ))^2*(Real.exp τ*τ^2)+V*τ) (carryFee N' Z₁ ψ'*(τ*rampFee gain L'.L) *fern L'.L^5) w:=by
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
    have ht : Temper R p.support p.site gain (G₁.main i) x τ:= htP.symm ▸ temperatures hb hh
    unfold Horn;
    have he':= Dust.Temper.flowers y0 χ 0 Z₁ P'' hP hg hT hn p.anchor hV' (1:Grid f) hq.le _ hwX (testG q K') (kinFare _ hv _ q ht' hq') ht (guard_silent χ hq (mul_pos D.guards R.threshold_pos)) hMQ hM (Q.halo+5)
    have hF:Zp = skimR (q ∘ S.ratio.parent) (testG q K') (proton L' G) (G₁.main i):=congr_arg (fun g=> skimR g (testG q K') (proton L' G) (G₁.main i)) hqg.symm
    rw [hF,← hsP]; exact he'
end YM.QCD.Shells
