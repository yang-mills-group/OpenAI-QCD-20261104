import YM.Mural.Breeze
import YM.Mills.Porch
import YM.Mills.Enthuse
import YM.Mills.Glow
import YM.MassiveQCD.Apron.Suppert
/-! # Larger value operator marker payments -- combined with a projection Shelf at small apertures separately. Also carries explicit amplified accounts for selections in the log beyond POLY covariance uses. Doesn't assert comparison to continuum Wick. -/
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
variable {c f s:Side}{P:Teller su}{δ β b τ μ W C d':ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l n i j k:ℕ}
variable {η p h z a a' t v V u u' q θ w₁ r:ℝ}{G₁: Plan j}{G₂:Plan k}
variable (L:Flight j k)(d:f.val=c.val*L.L.val)(O:KernelChoices)
variable {T : Tube su (Flight.visit L O d)} {W' :ℕ→Atom su 2} {P':Plan k}{X : St f}
variable {t0 a0 D U' A b' k0 θ' ε R' X' iP ip α y q' Ω:ℝ}
open Glow
open Kings Blaze Vine King
open MassiveQCD.Apron
lemma arborize (s:Side) {N m i j k:ℕ}{G₁:Plan j}{G₂:Plan k} (hc:CardT s N 38 36 C θ θ G₁ G₂ a b A D t θ p t0 Q.relative k0 Ω R' X' Q.relative i m z y q' q) (hv:0<θ)(hs:θ<1/8)(he:1 ≤k0)(X0 μ W:ℝ)(hl:0<μ)(hp:0≤X0)(o:Target.Order su W)(r b1:ℝ)(N₁:ℕ)(hr:0<r)(hb1:0<b1)
      (u η ε:ℝ)(h:u<p)(hα:0 ≤ α)(htα:α+1+1≤Q.exp)(hrQ: Q.rate ≤ -(3/8:ℝ))(hu:0<η)(huV:2*η<(1/32:ℝ)) (hU:∀ (c f:Side)(S:Ratio c f), S.count=s→ reserve u (Q.relative+1) (conversion S 38) ε) (hR:∀ (c f:Side) (S:Ratio c f), S.count=s→ reserve (1/32) (Q.relative+1) (conversion S 38) η): ∀ᶠ x in atTop,let I:=haloK s x; let v:=coneK s z x; let Z:=highW s k0 θ x; ∀ (c f:Side)(L : Flight j k)(H:f.val=c.val*L.L.val)(K:KernelChoices)(T:Tube su (Flight.visit L K H)),L.L=s→2*(radiusB x+1)<f.val →∀ (O:Garden.Offer 1 a A)(D': Garden.Offer 2 b D)(m':ℝ)(W0:ℕ→Atom su 2),|m'| ≤ wink s x → Extra.Iteration.Charged W0 t Ω→ Extra.Iteration.SymmetricAtoms W0→∀ (G:Sun L c f H v y q' p q i (park L H G₁ O D' I m'))(V:Swathe L H (park L H G₁ O D' I m') W0 G₂ y v p X' R' m) (R:BudgetPoint)(β b0:ℝ),let δ:=lowK s x P.top.supportExponent; ∀(Y:Cash W x μ L.L Q o X0 T (trimP T R δ β b0))(Xg: Land c (Site c) (Site c))(Zg:Pays c (Site c) (Site c)), Run.Pack id id r ((Q.relative*(10*preCost 37)+3)+1) N₁ (wood G₂ 0 L.land) b1 Xg Zg → ∀ F:Tree.Forest (Flight.visit L K H).ratio,∃ (u₁: Varn f c→ℝ)(u₂:Gaze c→ℝ), let B:=radiusB x; let S':=Flight.visit L K H; let v:=fan s (1/4) x; Stern (VarnC Y V N) F univ (fun i=>siteH i S'.ratio) u₁ Z v (univ.filter fun i=>waxV i=none) (18*B) (L.L.val^4+1) (fun i u _=>sliceF V N B i u) ∧ Stern (sailP Y Xg N) F univ Prod.fst u₂ Z v (univ.filter fun i=>i.2=none) (18*B) 1 (fun i=> dropG N Xg S'.ratio B i) ∧ Ac.Hit (VarnC Y V N).ground B (fun i=>Real.exp 1*u₁ i) Q.relative (betaF su x s^(-(3/8):ℝ)) ∧ Ac.Hit (sailP Y Xg N).ground B (fun i=>Real.exp 1*u₂ i) Q.relative (betaF su x s ^(-(3/8):ℝ)):=by
   let d:= Q.relative * (10* preCost 37)+3; have he' : reserve d Q.relative (10*preCost 37) 1:=by
      have ht:= Q.bound; have hv:= Q.usable; have ht':= Q.pos
      exact ⟨by unfold Target.relative; linarith,zero_lt_one,by unfold d; linarith⟩
   have hd':0 ≤ d:=by
     unfold d; have hA:=he'.1; have hm:0 ≤ preCost 37:=by unfold preCost; positivity
     positivity

   obtain ⟨f₀,hf,hF⟩:= hammock P s o.a o.large
   have hy':0<p:=hc.grow.wolf; let Cv:=max 1 C; have hCv:1 ≤ Cv:= le_max_left ..
   have hw : ∀ᶠ x in atTop,1 ≤ fan s θ x:=((Jets.Touch.Seat.your s).eventually_ge_atTop 1).mono fun i hi=> (Real.one_le_rpow hi hv.le)
   filter_upwards [hc.permit,hc.grow.pays,garrison hp (p:=d+1) (by linarith) hv hs he s N N₁ hr hb1.le hf P Q W o μ hd' he', hF, dipK s P.top.supportExponent, hw, Work.E01.radiusB_tendsto.eventually_ge_atTop 1,insoleP G₁ P s X' k0 z R' θ p o.a q' q y 0 i m N a b A D q 0 G₂ hf o.large hy' hc.grow.orbit (by linarith), Glow.royalties Q s θ hrQ hv hl hp,Glow.oversea (C:=X0) Q s θ hrQ hv hl hα htα,(Work.E09.betaF_growth su s).eventually_ge_atTop 1,rousing s N j k 38 i p Q.relative (1/32) u ε η θ Cv k0 q' hs h hv hCv (zero_lt_one.trans_le he),Fees.horizons su s 38 hu he'.1 huV] with x hp' hA hG hS hB ht hn hi hb hy hV hUp hz
   intro I v Z c f L H K TD hL hs0 O Ds m' W₀ hM hW hW' G V R β b₀ δ Y Xg Zg hxg
   subst s
   obtain ⟨hr0,hh0,hk0,hM0,hQ⟩:= hp' f c hs0 L H rfl O Ds m' hM; obtain ⟨hQ,hfQ⟩:=hQ W₀ hW hW'
   obtain ⟨hz',hZ⟩:=hfQ V; let S₁:=Flight.visit L K H; let VV:=trimP TD R δ β b₀
   let XU:= VarnC Y V N; have hT: S₁.ratio=sliceL L H:=rfl; have hJC:=Y.laws.data
   have hJ:=Y.laws.intake; have hR': R.threshold=fiery su x L.L:= hJ.received.temp
   obtain ⟨hb,hb'⟩:=hb β (show betaF su x L.L/2 ≤β from hJ.window.1)
   intro F
   obtain ⟨hg,hg'⟩:=hG c f S₁ TD VV rfl F (wood G₂ 0 L.land) _ _ hxg Y hS
   have hv' : Stern XU F univ (fun i=>siteH i S₁.ratio) (Port.shells V N (radiusB x) Z (coreRate L.L x)) Z (fan L.L (1/4) x) _ (18*radiusB x) _ (fun i u _=>sliceF V N (radiusB x) i u):= stilt Y V hT _ hz'  fun Y he he' hy i hh hg w hN=>by
     let Uv:= Y.liftA β w
     exact hi c f L H rfl O Ds m' hM hh0 W₀ V S₁ TD F Y rfl hJC.room hT he hy hS i hh Uv _ (marks i S₁.ratio (radiusB x)) hN hg
   refine ⟨_,_,hv',hg,hZ _ (fun i=>swaddled Y V i),hg'⟩
end YM.QCD.Loom
#print axioms YM.QCD.Loom.arborize
