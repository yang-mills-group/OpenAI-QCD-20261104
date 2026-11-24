import YM.Poised.Harp
import YM.Poised.Wreath
import YM.Poised.Garnish
/-!
# Accounts at all apertures. Covers actually Y^+ when using these. Bound with polynomial factor in length of input support (allows NOTshort in same currency).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG MassiveQCD.Plate MassiveQCD.Apron MassiveQCD.Elevator
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open AnalyticBridge.SectorAffine.Offset Planned.AtomRegular
open QCD.Dust QCD.Brick Pipes Spice MassiveQCD.Lyre Shells Sands MultiNext.SignedSource.Ease
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R Rx:Rep su f}{O O₁:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {δ y:ℝ}{H:Cash W τ μ L Q o C T (trimP T O δ β y)}{ι κ I E J D:Type}{N:ℕ}
variable {n p k d G l:ℕ} {a u r q v σ R z t w m γ α θ η :ℝ}{s:Side}
-- pre-L stipulations

variable {N':Libretto su n}
open Fountain WardBin.Lies MultiNext.SignedSource MultiNext.SignedSource.Lyre
-- zeta expense through any length order. late all.V.Univ B.Pl.Sub masks. Interval input choice.
structure Menus (P₁:Plan p)(N':Libretto su n)(E:Record)(p' p₂ D' U' k :ℕ)(K Yp:ℝ)(Vb:Hera.Rights su n)(Q: Target su P)(H:Patch)(L:Side)(W:ℝ)(o:Target.Order su W)(μ C u v t q a :ℝ)(l:ℕ)(χ:Chi)(x:ℝ)(s:ℕ)(γ:ℝ) : Prop where
   poses : ∃ A W₀ N₁ W₁ W₂ σ f5 g:ℝ,(∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→Through n (yaw i j) x A) ∧ 0 ≤ σ ∧ News P L x W Q o μ C n N' E χ p' W₁ W₂ g H ∧ ∀ (f':Side)(X: Support f') (O R:BudgetPoint),coverNumber R.B X ≤ s → R.B ≤ 2*radiusB x →R.threshold= fiery su x L→ R.power=p₂ → O.threshold=temp x→ O.power=p' → O.threshold≤2*R.threshold →∀ β:ℝ, betaF su x L/2 ≤ β →
       0<W₀ ∧ W₀≤1 ∧ 1 ≤ N₁ ∧(canopyW su L O.power x ≤ N₁* Heir.loom O (Heir.reach x) N'.C) ∧ FairT P₁ E N' D' l L x u v q a g f5 σ O ∧ (N'.M * (N₁* Heir.loom O (Heir.reach x) N'.C) ≤1)∧ (1+patterns n)*(A*(N'.M*(N₁* Heir.loom O (Heir.reach x) N'.C)))*((Fintype.card Pipes.Shell:ℝ)*Yp) ≤ W₀ ∧ Cub.opal N' E O R L X (Q.halo+5) x (gStep β)*N₁^n ≤ W₀ ∧ (∀ b: Site f', b∈X→∀ i,Mom.needed X i→ Lyre.width R b i≤1) ∧
       (∀ d0<U', ∀ z:ℝ, 0 ≤ z → ((d0:ℝ)*(K*2^D'*σ)*Yp^d0*z)*|W₁| + Yp^d0*z*|W₂|+ Fountain.sheen d0 Vb W₀ Yp*z*AnalyticBridge.LocalGaussian.Moments.meter (Heir.Lute.heads su R L X (Q.halo+5) x) 0 E.K (2*((n+1)+(n+1)))≤ γ*z) ∧
       ∀ c (P': Flight p k)(h:f'.val=c.val*P'.L.val)(v₀ u₀ p₀ p₂:ℝ)(E:Offer 1 v₀ u₀)(V:Offer 2 p₀ p₂)(m:ℝ)(G:Sun P' c f' h (coneK L v x) t q u a l (pesto P₁ P' h (trunkM E V (haloK L x) m f'))),P'.L=L → 2*(radiusB x+1)<f'.val → |m| ≤haloK L x→ Consider D' (K*2^D') G (radiusB x) R.threshold
lemma sheen_live (C:Hera.Rights su n)(L :Side)(S q₀:ℕ)(p:ℝ)(w:ℝ→ℝ)(h:Seat L (-1) w):Seat L (-1) (fun x=> sheen S C (w x) p):=by
   let W:= sheen S C 1 p; refine Seat.equal (h.times W) (Eventually.of_forall fun x=>?_); change _=w x*W; unfold W Fountain.sheen; ring
-- choose.D order uniform through β costs.W.N.A.Crypt.
lemma diplomatic (P₁:Plan p)(k D' :ℕ)(K:ℝ)(h:4 ≤ p)(ht:4 ≤ k)(hK:1 ≤ K): ∃ n:ℕ,∀ L: Side,n≤L.val →∀ (H:Patch)(Q:Target su P), H.Branches P.bind su →∀ (n p' p₂ U':ℕ)(N':Libretto su n)(E:Record)(Yp:ℝ)(Vb:Hera.Rights su n)(W:ℝ)(o:Target.Order su W)(μ C u v t q a :ℝ)(l:ℕ)(χ:Chi)(s:ℝ→ℕ),Seat L 0 (fun x=>(s x:ℝ))→2 ≤ n→ E.ε≤1/4 →0<u→0<v→1≤Yp→∀ᶠ x in atTop, Menus P₁ N' E p' p₂ D' U' k K Yp Vb Q H L W o μ C u v t q a l χ x (s x) (fan L (-1/2) x):=by
    obtain ⟨n,hN⟩:= diamondsP P₁ 6 D' h ht (K*2^D') (by positivity); refine ⟨n,fun L hL H Q hQ n p' p₂ U' N' E Yp Vb W o μ C u v t q a l χ s hσ hn he hu hv hk=>?_⟩; obtain ⟨A,hA,hP⟩:= charterY n
    obtain ⟨W₁,W₂,g0,h1,h2,h3,hg⟩:= Sands.spirit (Q:=Q) (μ:=μ) (C:=C) (o:=o) L N' E χ H hQ he hn p' 0
    obtain ⟨W0,N,M,hM,hS,hW,hΩ⟩:= tithing N' E L p' p₂ 0 0 A Yp hk (zero_le_one.trans hA) (Q.halo+5) s hσ
    obtain ⟨f5,σ,hf,h,hD⟩:= trophies P₁ N' E p' D' l L u v q a hu hv g0 h3
    let Q₁(x:ℝ)(d:ℕ):= (((d:ℝ)*(K*2^D'*σ x)*Yp^d)*|W₁ x| + Yp^d*|W₂ x| + sheen d Vb (W0 x) Yp * M x)
    have hK' (d:ℕ): Seat L (-1) (fun x=> Q₁ x d):=by
        have hp:Rate su L 0 (fun x=>|W₁ x|):=Rate.compare h1 (Eventually.of_forall fun i=> (abs_abs _).le); have hh:Rate su L (-(1/2)) (fun x=>|W₂ x|):=Rate.compare h2 (Eventually.of_forall fun i=> (abs_abs _).le)
        have hL: Seat L (-1) (fun x=> sheen d Vb (W0 x) Yp*M x):=by simpa only [add_zero] using! ((sheen_live Vb L d 0 Yp W0 hW).ponies hM)
        exact Seat.comb ((Seat.eliminated ((((h.mul_left (K*2^D')).mul_left (d:ℝ)).mul_right _).mul hp) (by norm_num)).comb (Seat.eliminated (hh.mul_left _) (by norm_num))) hL -- .timesL' change
    have hJ:= eventually_all.mpr fun i:Fin U'=> hK' i (-1/2) (by norm_num)
    filter_upwards [hg, hΩ,hD,hN L hL v u q a hv hu l,hJ] with x he hΩ hD hN hJ
    obtain ⟨hyX,hθ,hθ'⟩:=hD
    -- prices positivity unconditional via budgets need B,R exist with heights,Order after.B.W.Include head.Z only implications instead. tithing exposes through P,R β. adjust
    refine ⟨⟨A,W0 x,N x,W₁ x,W₂ x,σ x,f5 x,g0 x,hP,hθ,he,?_⟩⟩; intro f X O R hX hR hτ hK2 ht hv' hh β hβ
    obtain ⟨g1,g2,g3,g4,g5,g6,g7,g8⟩:=hΩ β hβ O R hR hK2 hτ ht hv'; obtain ⟨k1,k2,k3⟩:=g8 _ _ hX
    refine ⟨g2,g4,g1,hv'.symm ▸ g5,hθ' _ (hτ ▸ hh) hv',g6,g7,k1,k3,?_,?_⟩
    · intro i hi Z hZ; apply le_trans _ (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hJ ⟨i,hi⟩)) hZ); have h0:0 ≤ sheen i Vb (W0 x) Yp:=by have h:=Vb.large; unfold sheen Pipes.mouth; positivity [patterns_nonneg n]
      apply (add_le_add_right (mul_le_mul_of_nonneg_left k2 (show 0≤ sheen i Vb (W0 x) Yp* Z by positivity)) _).trans_eq; change _=Q₁ x i * Z; unfold Q₁; ring -- left?
    intro c P' h v₀ u₀ p₀ p₂ E V m G hD hN' hW
    obtain ⟨u₁,hx,hm⟩:= hN _ _ hN' P' h hD t v₀ u₀ p₀ p₂ _ _ _ hW G -- fix
    exact ⟨u₁, hτ.symm ▸ hx,hD.symm ▸ hm⟩
end YM.Massive.Poised
#print axioms YM.Massive.Poised.diplomatic
