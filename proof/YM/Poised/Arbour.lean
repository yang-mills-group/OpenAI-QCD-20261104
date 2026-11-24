import YM.Poised.Scrips
import YM.VStages.Municipal
import YM.VStages.Precedence
/-! # common track finance reservation after choosing rank. Unmarked policy.Erf at all binder stages. -/
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
variable {P:Teller su}(Q:Target su P)
variable {N m n l i j k:ℕ}{C A D η p h z a b t v u u' q θ:ℝ}
variable (P₁:Plan j)(P₂:Plan k)
open Blaze King March GasP Ursell Stew Patron
open Shells Sands
open PhysicalNext.Repeat PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Dust Brick
open MassiveQCD MassiveQCD.Plate MassiveQCD.Apron MassiveQCD.Lyre
open QCD.Acre QCD.Acre.Stratum QCD.Acre.Stratum.MarchQ
open QCD.Raft QCD.Raft.ParcelR
variable (χ: Chi) (τ: Policy Q P.below N)
-- independent Ω. heater type
def Portion (L:Side)(W μ C h K d t q η a α u:ℝ)(o:Target.Order su W)(l:ℕ)(D':Patch)(D:Heir.Record)(χ:Chi)(Kq:ℕ)(H₁:Libretto su n)(x:ℝ) := ∀ (c f:Side)(S:Flight j k)(H:f.val=c.val*S.L.val)(Z: KernelChoices)(T:Tube su (S.visit Z H)), (S.visit Z H).patch=D' → S.L=L→ Works P L x (Flight.visit S Z H) T → 2*(radiusB x+1)<f.val →∀ (R R' O:BudgetPoint) (β δ β' mm a₀ b₀ a₁ b₁:ℝ)(E₁:Offer 1 a₀ a₁)(E₂:Offer 2 b₀ b₁) (G:Sun S c f H (coneK L d x) t q η a l (pesto P₁ S H (trunkM E₁ E₂ (haloK L x) mm f)))
   (W':ℕ→Atom su 2)(v y:ℝ)(p':ℕ)(V:Swathe S H (pesto P₁ S H (trunkM E₁ E₂ (haloK L x) mm f)) W' P₂ t (coneK L d x) η v y p') (Q₀:Land c (Site c) (Site c))(B₀:Cash W x μ S.L Q o C T (trimP T R δ β β'))(B₁: Cash W x μ S.L Q o C T (lore (trimP T R δ β β')))(B₂:Cash W x μ S.L Q o C T (lore (trimP T R' δ β β'))),|mm|≤haloK L x → betaF su x L/2≤ β → R.threshold= fiery su x L → R.threshold=R'.threshold →R.B=highR L x→ R'.B=R.B→ Seats B₀ χ → Plays H₁ D O R' P T x→ O.B=radiusB x → O.power=Kq →
   ∀{I E J:Type}[Fintype I][Countable E][Countable J] (Y:Rise f N E J)(A:I→Site f)(p:I→Bool)(φ:ℝ)(V₁:MassiveQCD.Stitch.Tablet Y I) (σ:E→ℝ)(ζ:J→ℝ), let T':= fan L h x; φ≤K*T' → Cents Y σ ζ T' R.threshold → Fill Y σ ζ u u (taxK L x 1) 1 (chip L x) (highR L x)→ V₁.Coins σ ζ T' R.threshold → (∀ e, σ e≤ chip L x)→∀ (a b:ℝ), MassiveQCD.Apron.Grove.Supplies S H Z B₀ G V Q₀ V₁ A φ χ p a b O.order O.power → Patrol (O₁:=R') S H Z B₀ G V Q₀ V₁ A φ B₁ χ O T' α (fan L (-h/4) x*chip L x) p σ
open Massive.Poised Massive.Poised.TrainG Rails
structure Boardlet (J:Patch)(W μ C:ℝ)(o:Target.Order su W)(α a:ℝ) (H:Massive.SourceRead.TaperHol)(n' p E' Z₀ Gh Kq Gn U' D':ℕ)(A₁ A₂:ℝ)(N₀:Libretto su n')(V:Hera.Rights su n')(X:ParcelR) (x:ℝ):Prop where
    sealR:∃ D:Heir.Record, TrainG.Ledger P₁ Q J N₀ D o μ C τ.X.c τ.X.r τ.X.b τ.X.a τ.X.Q τ.X.i k Z₀ χ H V p E' Gh Kq Gn U' D' (eraF N) A₁ A₂ x ∧ Portion (N:=N) Q P₁ P₂ J.L W μ C τ.t (eraF N) τ.X.r τ.X.b τ.X.a τ.X.c τ.X.Q α a o τ.X.i J D χ Kq N₀ x ∧ VoucherInk P₁ P₂ Q J X W μ C o χ τ n' Kq x ∧ wink J.L x ≤ haloK J.L x
lemma cellarQ (χ:Chi)(N ℓ Kq Gh Dd p q i d z:ℕ)(H:Massive.SourceRead.TaperHol)(Hp:Hera.Rights su n)(α a b u θ:ℝ)(hA:0<a)(hb:0≤b)(hα:0 ≤ α)(hU:0<u)(ht:0<θ)(hk:6 ≤ n)(hr:d<n)(hx:n ≤ ℓ)(hμ:0<P.C)(hj:4≤j)(hk':4≤k)(hG:q ≤ P.j-2)(hQ:q≤ j-2)(hh:q≤Gh)(hg:Kq≤Gh)(hm:2≤Gh)(he:q ≤ Dd)(hy:p ≤2*q+2): ∃ (N₀: Libretto su n)(A₁ A₂ feeQ:ℝ)(l' :ℕ), Prebit Q j k Gh p Dd Kq N₀ (eraF N) A₁ A₂ a b feeQ l' ∧N₀.δ=P.η∧ N₀.N=P.C∧∀ (τ: Policy Q P.below N)(ν s:ℝ)(J: Patch)(W μ C:ℝ)(o:Target.Order su W)(X:ParcelR), J.Branches P.bind su → τ.t=θ→MicroPay τ μ ν s→ l'≤ J.L.val →(∀ᶠ x in atTop,VoucherInk P₁ P₂ Q J X W μ C o χ τ n Kq x)→∀ᶠ x in atTop,Boardlet Q P₁ P₂ χ τ J W μ C o α u H n p i d Gh Kq ℓ z Dd A₁ A₂ N₀ Hp X x:=by
     obtain ⟨H₁,C,C',L,n1,hP,h1,h2,hJ⟩:= TrainG.stable _ Q P₁ k Kq Gh Dd p q i d z ℓ H Hp (eraF N) a b hA hb (earns N) hk hr hx hμ hj hk' hG hQ hh hg hm he hy
     obtain ⟨n2,H2⟩:= Loom.reward Q P₁ P₂ χ N θ (eraF N) α u 1 hj hk' ht zero_lt_one hU (earns _) hα
     refine ⟨H₁,C,C',L,n1+n2, ⟨hP.lore,hP.span,fun L h=>hP.tax L (by omega)⟩,h1,h2,?_⟩; intro τ ν s J W μ D o X hΩ hθ hQ hN hx; obtain ⟨V,hv⟩:= hJ J.L (by omega) J rfl hΩ; have hz: 0<τ.X.c:= hQ.inches.symm ▸ zero_lt_one
     have h':= hv W μ D τ.X.c τ.X.r τ.X.b τ.X.a τ.X.Q τ.X.i o χ hz hQ.steady
     obtain ⟨g,hM⟩:= h'.exists
     have ht := H2 J.L (by omega) W μ o D τ.X.r τ.X.b τ.X.a τ.X.Q τ.X.i hQ.steady J hΩ rfl V n H₁ Hp Kq hM.haloP (by omega)
     filter_upwards [ht,h',hx,pops J.L 1 1 zero_lt_one] with x ht hy he hz; constructor; refine ⟨V,hy,?_,he,?_⟩
     · rw [hθ,hQ.inches]; exact ht
     exact hz.1 -- inspect
end YM.QCD.Loom
#print axioms YM.QCD.Loom.cellarQ
