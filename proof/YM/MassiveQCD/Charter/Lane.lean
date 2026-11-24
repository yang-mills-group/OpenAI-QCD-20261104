import YM.QCD.House.Toast
import YM.MassiveQCD.Charter.Paint
import YM.QCD.Pant.Inlet

/-! # The lamps for ALL clocks (basis is not a Point in a Grassmann phase)

Require existence of all ports on the weaker symmetry, through enhancements as necessary.
`PortC` and `Colored` preserve *color* not flavor indices. Even complex marker calculations in
value norms may be charged immediately. The same ports promise old `PortD` in the Pant basis.

These are bare ledger-integral prices, NOT emitter output published estimates; especially
there are no jet budgets in `PortC` (see `Calendar`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Villa
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Cove Leaf Lat Creek Loom
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass Sway OrbitG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{P:Teller su}{δ β b τ μ W C:ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l n i j k:ℕ}
variable {Y:StepData c f} {η p h z a a' t v u u' q:ℝ} {D E J:Type}[Countable E][Countable J][Fintype D]
open AnalyticBridge.GaussianFieldAlignment Locations Channels PhysicalNext.Repeat.Turn Next.Fluctuations Next.SectorChange
local notation "B" => radiusB τ
open Sway OrbitG Strut Revolve
variable {W' :ℕ→Atom su 2}{J':Plan k}
variable (O:Flight j k)(K: KernelChoices)(d:f.val=c.val*O.L.val)
set_option quotPrecheck false
local notation "S"=> (O.visit K d).ratio
variable {T : Tube su (O.visit K d)}
variable {X:Grid f→Sheet f} (H:Cash W τ μ O.L Q o C T (trimP T R δ β b))(G:Sun O c f d η h z a a' m X) (U :Swathe O d X W' J' h η a u v i)
variable {Γ: Land c (Site c) (Site c)}{D':Pays c (Site c) (Site c)}
variable (Y': Rise f N E J)
local notation "Z'"=> tableau O d K Y' H G U Γ
open PhysicalNext.Repeat.Greenbelt Territory GasP Ursell Graph
open scoped PhysicalNext.Repeat.Greenbelt
-- Receipt all real; with Penalty tickets launch in code, no downstream jets/projectors!
open Patron
structure PortC (Y': Rise f N E J) (L:Land c (Site c) (Site c))(θ a v:ℝ) :Prop where
    color : Colored (tableau O d K Y' H G U L)
    mask : Pant f N R.threshold Y' → Pan O K d H (tableau O d K Y' H G U L)
    wordsP : (tableau O d K Y' H G U L).speaking
    within F : Within O d K Y' H G U θ a F L
    scores χ : let Z:= tableau O d K Y' H G U L
               let t x:= honest Z χ x; let q x:= NormedSpace.exp (∑' i,t x i)*(∑' i,Z.ket χ x i)
               let P':= trimP T R δ β b
               (∀ V, Summable (t V)∧ Summable (ket Z χ V) ∧ HasSum (fun i=> Z.emergingF i χ V) (q V)) ∧
                 (∀ V,∀ F:Tree.Forest (O.visit K d).ratio,
                     let X1:= prism T τ χ o.K V F
                     ((O.visit K d).push β (Emitter O d K Y' T δ β b R W' X) V)=(X 1).det^N • (Cove.light _ (Matter.overhead X1 P' Q.table • q V)*gauss (Lat.copies N (wood J' 0 O.land V)))) ∧
               (∀ s:Z.Faber, Measurable (fun V=>Z.mission χ V s.val) ∧ UsesFinal (Pressure.temp τ) (GasP.wound Z.broad s.val) (fun V=>Z.mission χ V s.val)∧ (∀ V, Gated (GasP.wound Z.broad s.val) (Z.mission χ V s.val))) ∧
               (∀ s:Clusters Z.Bright, Measurable (fun V=>Z.furnace χ V s) ∧ LocalOn (seatP Z.lightF s) (fun V=> Z.furnace χ V s) ∧ ∀ V,Gated (seatP Z.lightF s) (Z.furnace χ V s)) ∧
               let b:= Fleet.crownQ O.L θ μ C τ (shiftCost O.L τ (romp O.L)) β Q
               ∃ g:Z.Faber→ℝ,(∀ V,∀ x: Z.Faber,‖token c N a (Z.mission χ V x.val)‖ ≤ g x)∧ Ac.Hit (fun x:Z.Faber=>GasP.wound Z.broad x.val) (radiusB τ) (taxed (fun i:Z.Faber=> sweep Z.invD i.val) g (Real.exp b.markSeed)) v 1
variable {θ v' α α' m₀ a₀ b₀:ℝ}
set_option maxHeartbeats 600000 in
lemma dew_colored (hs:∀ F, Within O d K Y' H G U θ α F Γ)(hc:Colored (tableau O d K Y' H G U Γ))(hp:Pant f N R.threshold Y' → Pan O K d H (tableau O d K Y' H G U Γ))(hsay:(tableau O d K Y' H G U Γ).speaking)(ht:0<radiusB τ)(hv:0<α)(hJ: Corner Q (radiusB τ) (crownQ O.L θ μ C τ (shiftCost O.L τ (romp O.L)) β Q) v') :PortC O K d H G U Y' Γ θ α v' :=by
    refine ⟨hc,hp,hsay,hs,fun χ=>?_⟩
    intro Z t' q R'
    let F:= Classical.choice (Tree.select (S) O.odd)
    have he: Z.Famous:=(hs F).1; have hF:Z.Feasible:=Villa.validH O K d H G U Y' ht; have hw: Territory.Gate Z:= ⟨(hs F).2.1⟩
    obtain ⟨w,h⟩:= Villa.loan O K d H G U Y' hs
    let b:= crownQ O.L θ μ C τ (shiftCost O.L τ (romp O.L)) β Q
    have hh V:= Fleet.beck Z he hF h hJ hv χ V
    refine ⟨fun V=> ⟨(hh V).1,(hh V).2.1,(hh V).2.2.1⟩,?_,?_,fun s=> ⟨(Z.courtB he hsay χ s).1,(Z.courtB he hsay χ s).2,fun i=> Z.sensesP he hw χ i s⟩, ⟨fun i=> tenderW Z.broad Z.lightF i.val (fun j=> grass Z w b j.val) (fun j=> grass Z w b j.val),fun V=>(hh V).2.2.2.1,(hh 1).2.2.2.2⟩⟩
    · intro V F X'; have hf:= star_push O K d H G U Y' hs F V χ; apply hf.unique; let L:= Loom.Y'' (gauss (Lat.copies N (wood J' 0 O.land V))) ((X 1).det^N); let Hm:= Matter.overhead X' R' Q.table
      change HasSum (fun i=>L (Hm • (Z.emergingF i χ V))) (L (Hm • q V)); have hG : HasSum (fun i=>Z.emergingF i χ V) (q V) := (hh V).2.2.1; exact L.hasSum (hG.const_smul Hm)
    haveI : Countable Signed:= by infer_instance
    haveI : Countable (Site c):= by infer_instance
    haveI : Countable (Site f):= by infer_instance
    haveI : Countable PlaqAxes:= by infer_instance
    haveI : Countable (Raw.LogLetter c f):=by unfold Raw.LogLetter Raw.Trans Raw.Pairs; infer_instance
    haveI : Countable (Miniature c f):=inferInstance
    haveI : Countable (WarningAt c f):=inferInstance
    haveI : ∀ n,Countable (Ledger f n):=fun n=>by unfold Ledger; infer_instance
    haveI : Countable (ChainIndex f):=by unfold ChainIndex; infer_instance
    haveI : Countable (Head (O.visit K d)):=by unfold Head Mixed.Alphabet ConnectedActivityE6.Alphabet LogIndex; infer_instance
    haveI : Countable Z.Bright:=by unfold Bright Pipe.Clump Pipe.Piece; infer_instance
    intro s; exact Z.inletC he hF hw hsay χ s.val

omit [Countable E] [Countable J] in
lemma PortC.original (hp:PortC O K d H G U Y' Γ θ t v') (hθ:Pant f N R.threshold Y') : PortD O K d H G U Y' Γ θ t v':=⟨hp.mask hθ,hp.within,hp.scores⟩
lemma PortC.meta (hV: PortC O K d H G U Y' Γ p t q) (hB:0<radiusB τ) : (Z').Famous ∧ Territory.Gate (Z') ∧ (Z').Feasible:=by
    let F:=Classical.choice (Tree.select S O.odd)
    exact ⟨(hV.within F).1,⟨(hV.within F).2.1⟩,validH O K d H G U Y' hB⟩
lemma iris_color (hp:Y'.Reframe) (hW:Y'.Wave R.threshold)(hh:Run.Pack id id t p n (wood J' 0 O.land) q Γ D')(hr:0<t)(hG:0<η): Colored (Z')∧ (Z').speaking:=by
   let F:= G.equip N B; let Y:= roof F Y' 30 B; let A:=deckHue H F Y' Y; let T':= VarnC H U N; let Z:=sailP H Γ N
   have hs: S=sliceL O d:=rfl
   let l (z:Lat.Frame c):= constantGauge z S; have h z:(l z) ∘ (S).embed=z:= funext fun i=>congr_arg z ((S).embed_parent i)
   refine ⟨⟨?_⟩,Fleet.voice A (hue_voice H F Y' hW) (Fleet.voice T' (varnV H U hG) (Villa.visible H hh hr))⟩ -- `voice` ambiguous check
   · intro z'; let P:=trade (rotates N (l z')); let T':=trade (rotates N z') -- shadow
     have hf: trade (rotates N z')= trade (rotates N ((l z') ∘ (S).embed)):=by rw [h]
     have he X: Usher S F (Lattice.gauge (l z') X) X (trade (whole (rotates N (l z')) (rotates N ((l z') ∘ (S).embed)))) P (trade (rotates N z')) (Equiv.refl _) (Equiv.refl _):=by rw [hf]; exact Sway.heatE G N B X _
     refine graft A (gaugeP H F Y' z' he (fun U=> Loom.outfit H Y' hp U _)) (graft _ (boon H U _ z' ?_) (Villa.mesh H hh z'))
     rw [hf]; exact fun i U'=> triumph U N B i _ _
end YM.QCD.Villa
