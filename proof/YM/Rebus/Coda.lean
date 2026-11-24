import YM.Rebus.Fire
/-! # Payload pricing projections. One-vertex estimate for common-tile.Id.Loan.Pν normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Rebus
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot Apron Apron.Grove
open Play.Camp Stitch
open scoped Topology Matrix InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{P:Teller su}{β τ C μ W s v κ' κ₁ p₀ q₁ q₂ r' r t t' A₀ A₁ B' u u' s' σ θ η η₁ h' x x' a a' w w' z b v' Ω' φ ε :ℝ}
variable {O:BudgetPoint}{ι κ I E J D: Type}[Fintype I]
variable {N i j n k m l B Q t₀: ℕ}
-- exported accounting for scripts.
variable (L':Flight i j)(h:f.val=c.val*L'.L.val)(K: KernelChoices)
variable {X: Run.St f}{T:Tube su (Flight.visit L' K h)}{F:Tree.Forest (Flight.visit L' K h).ratio}
local notation "Sⁱ"=> Flight.visit L' K h
local notation "R"=> sliceL L' h
variable {Q': Target su P}{o:Target.Order su W}
variable (H:Cash W τ μ L'.L Q' o C T (trimP T O r' β b))
variable (G:Sun L' c f h η h' z a a' m X)
set_option quotPrecheck false
variable (Z:Rise f N E J) (A: Stitch.Tablet Z I) (V₀: Finset (Finset I))(S': Finset E)(p:I→ Site f)(q:I→Bool)
local notation "xp"=> (sliceL L' h).parent∘ p
variable (Φ : Quince f N I)
local notation "Ap"=> spineP p N (majorT l*O.B)
local notation "Aw"=> can p (majorT l*O.B)
local notation "βg"=> gStep β
variable (gT:Hypnos.State su)(u t:ℝ) (V: Directions su c) (Y:Coat T F) (Jz: Air f su)
local notation "HX"=> βg
local notation "B0"=> radiusB τ
local notation "Vv"=> increment 1 V
local notation "Y1"=> karm κ₁ Vv
variable {Vp d mξ D' A₂ ιp h₈ :ℝ}
variable (Xz:Finset I)
local notation "Xy"=> shock Xz (Ap)
local notation "Xw"=> shock Xz (Aw)
local notation "Wx"=> heather xp (radiusB τ) Xz
variable {w0 w1:Clip}(J₀ J₁:Bed)(Tx:Towers (Flight.visit L' K h).patch.L) (AxP:Striation (T:=T) J₀ J₁ Tx w0 w1 s s')
variable (M₀:Myth su (Flight.visit L' K h) J₀ J₁ Tx (radiusB τ) Vp t)
local notation "X0"=> Dh f N I
local notation "X1"=> Dh c N I
variable (hV₁ : Y.manifest)(hV₂:Y.x=τ)(hV₃:Y.width=o.K)
local notation "YP"=> Y.input (Y.liftA β Jz)
variable (hc:∀ i∈heather ((sliceL L' h).parent∘p) (radiusB τ) Xz, ¬Inside i Y.seeds (30*Y.B))
-- `φ` is max radius actual V reachable. `r`: tile schedule previous, may be smaller; use either. 
local notation "Yk"=> karm βg YP
local notation "Kw"=> Fruit.cones su (Flight.visit L' K h) J₀ J₁ Tx (radiusB τ)
local notation "Qw"=> Oce.surge (dove F) (Kw  *ᵥ Y1) Jz
-- v threshold parent. `A₂` comparison budget post-L t from StepPrice. Match.W.C.Public
set_option quotPrecheck false
local notation "ST"=> swapV v φ |D'| mξ d gT.web.scale Vp t
local notation "Zr"=> Cape.cups p (majorT l*O.B) Xz
variable (hVk : ‖V‖≤ v) (hK': Y.V=increment 1 V)(htg:v≤ gT.r)
-- helper pure μ frame test all actual pickups
local notation "Vb"=> Anomaly.splash (Anomaly.breezeP (Spine I) ((G.equip N (radiusB τ)).shortP YP)) (Anomaly.breezeX (Spine I) (stamping (spore G (radiusB τ) YP)))
local notation "KV"=> kpit L' h N B0 I
local notation "KZ"=> sfan L' h N B0 I
local notation "KF"=> Anomaly.splash KV KZ
local notation "p₁"=> parties Φ Xz
local notation "Av"=> Anomaly.breezeP (Spine I) ((G.equip N (radiusB τ)).shortP YP)
local notation "Aw'"=> Anomaly.breezeX (Spine I) (stamping (spore G (radiusB τ) YP (F:=N)))
-- allocate p all spin local. share Planet. w,w' could choose exposure both. quoteN after-L trajectories step.
variable {M₁ M₂ M₃ b₁ a₁ h₇ θ₁ E' D₀ D₁:ℝ}
variable (hS: Spins L' h N (radiusB τ) M₁)
local notation "nk"=> l*t₀
local notation "Ω"=> Anomaly.shiver (l*t₀) M₃ M₃ (stockN N (radiusB τ)*M₂) M₂
local notation "ζ"=> A₂^(l*k)*h₈
local notation "F1"=> Apron.Grove.puddle A S' (Y.input (Y.liftA β Jz)) (O:=O)
local notation "F0"=> Oce.rose X0 Yk
-- cost frames reduce
variable {cp cb te PS₀:ℝ}(YS:Yield L' h K gT J₀ H v v' cp φ D' cb te)
-- bridge covariance. cp lens. govern small actual permit stage.
variable (hηv:0≤ Vp) (hη1:1≤ Vp)
variable (hCp: TileW L' h K H Z A V₀ S' p q Xz r ε h₈ k t₀ l Φ)
-- grade particular costs. Numerics may require sign field.E
local notation "Q0"=> (raw L' h K J₀ J₁ Tx B0)
local notation "QZ"=> (sineP L' h K J₀ J₁ Tx (solace J₀ J₁ Tx AxP) B0)
local notation "cφ"=>cents p₁
variable {θ' α:ℝ}
-- pure forecast.K pays
local notation "PP"=> AnalyticBridge.LocalGaussianLaws.Current.curlTariff su (Flight.visit L' K h).patch 0
variable (hp2: Vp ≤ M₃)(hT2: M₁≤ M₃)
variable (hD2: θ₁ + Vp ≤ M₃) (hlθ:0 ≤ θ₁) -- υ' compared kernel budget small
private lemma pane_hold {A:Type}(Q R₀: Next.Rank.Normal.Symmetric A)(G: Finset A)(t t' :ℝ)(h:Bera.Pane Q G t)(hQ : Bera.Pane (R₀+-Q) G t'): Bera.Pane R₀ G (t'+t):=by
    intro i hi j hj; apply le_trans _ (add_le_add (hQ _ hi _ hj) (h _ hi _ hj)); change ‖R₀.cov i j‖ ≤ ‖R₀.cov i j+ -Q.cov i j‖+‖Q.cov i j‖; simpa only [←sub_eq_add_neg,sub_zero] using norm_sub_le_norm_sub_add_norm_sub (R₀.cov i j) (Q.cov i j) 0 -- simp?
-- salutation abs at rotation boot.V.
include YS hV₂ hV₁ hV₃ hK' hc hVk
lemma pointV : Y.relating.PosSemidef := (YS.holds F Y hV₂ hV₃ hV₁ Wx V hVk hK' hc).1
local notation "Qx!"=> groveV F Y (pointV L' h K H p gT V Y Xz J₀ hV₁ hV₂ hV₃ hc hVk hK' YS) -- order
-- even without forecast progress.L.M3 may derived eventually.Shelf fee hPC must β ex.
omit YS hV₂ hV₁ hV₃ hK' hc hVk
include AxP M₀ hp2 hT2 hS hη1
lemma upbeat (A B:Finset I): Sky (Q0) QZ KV KZ (shock A Aw) (shock B Ap) M₃ M₃ M₃ M₃ :=by
    -- independent noise windows. OK post Budget. 
    have hz:= sailing L' h hS (shock B Ap); have ht:= hS.pos.trans hT2
    refine ⟨ht,zero_le_one.trans ht,ht,zero_le_one.trans ht,fun i hi=> (auraV J₀ J₁ Tx M₀ (shock A Aw) i hi).trans hp2,fun i hi j hj=> (chordV J₀ J₁ Tx AxP M₀ (shock A Aw) i hi j hj).trans hp2,fun i hi=> (hz.1 _ hi).trans hT2,fun i hi j hj=> (hz.2 _ hi _ hj).trans hT2⟩
include YS hV₂ hV₁ hV₃ hK' hc hVk hCp hD2 hlθ
set_option maxHeartbeats 500000 in
lemma tuneK (hPC: AnalyticBridge.LocalGaussianLaws.Current.curlTariff su (Flight.visit L' K h).patch 0 * PP*cp+t ≤ θ₁)(hY: Y.relating.PosSemidef) :
    Bera.Pane (groveV F Y hY) (shock Xz Aw) M₃ ∧ Sky Q0 (groveV F Y hY) KV KZ Xw Xy M₃ M₃ M₃ M₃ ∧ drifts Q0 (groveV F Y hY) KV KZ Q0 QZ KV KZ Xw Xy θ₁:= by
      have ht:= YS.holds F Y hV₂ hV₃ hV₁ Wx V hVk hK' hc
      have hp:0<B0:=(by have ht:= H.laws.data.room.sight; omega)
      let Q:= groveV F Y hY; have hC:= hCp; have hY: Bera.Pane (Q+-QZ) (shock Xz Aw) θ₁:=fun i hi j hj=> (earnedK J₀ J₁ Tx AxP F M₀ Wx Y (shock Xz Aw) hY (gaugeFt R p hC.mast hC.arch hp _) H.laws.data.room.larger YS.bill ht.2.1 i hi j hj).trans hPC
      have he:=pane_hold QZ Q (shock Xz Aw) Vp θ₁ (chordV J₀ J₁ Tx AxP M₀ _) hY; have hf:Bera.Pane Q (shock Xz Aw) M₃:= fun i hi j hj=> (he _ hi _ hj).trans hD2; have hx:=upbeat L' h K (O:=O) (l:=l) (hp2:=hp2) p t J₀ J₁ Tx AxP M₀ hS hη1 hT2 Xz Xz -- order.
      refine ⟨hf,⟨hx.craze,hx.heel,hx.dot,hx.buck,hx.gu,hf,hx.po,hx.trib⟩,fun i _=> ?_,hY,fun i _=>?_,fun i _ j _=>?_⟩ <;> simp only [sub_self,norm_zero,Matrix.zero_apply,Finset.sum_const_zero] <;> first| exact hlθ|skip
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.tuneK
