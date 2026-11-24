import YM.QCD.Kites.Bake
import YM.QCD.Fall.Sail
/-! # publication under budgets. Keeps old unmasked spectator & alpha receipt. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kites
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε S A':ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr
variable {Γ:Silo c}{X:St c}{ι β ν α ι':Type}
local notation "V'"=> EvenA c N
variable (G: Gem c N ι)(F: Rail c N β)(Y: Ruby.Hue c N ν) (W:Gem c N α)(Y': Ruby.Hue c N ι')

open Pressure Jets.Touch

lemma bearKR (L:Side)(M a:ℝ)(h:0 < M)(he:0≤a): ∀ᶠ x:ℝ in atTop, ∀ (c:Side)(N:ℕ)(ι β:Type)(Y:Ruby.Hue c N ι)(X:Rail c N β)(p:BudgetPoint)(t:ℝ), p.B=radiusB x → Quits X p.B 1 (priceK L M x) (a+1) t → Purchases Y p.threshold p.B (a+1+1) (pra L x) t → Quits (Ruby.Trail Y X p.threshold) p.B 1 (taxK L x 3) a t :=by
   filter_upwards [Ruby.portendsR L M a h he] with x hx; intro c N ι β Y X p t ht hp hz; obtain ⟨g,hg,hX⟩:=hp.cost; obtain ⟨y,hy,hY⟩:=hz.paint; rw [ht] at hY hg ⊢
   have he : 0≤ g:=fun i=> (norm_nonneg _).trans (hX i 1); have he':0≤y:=fun i=> (norm_nonneg _).trans (hy i 1); refine ⟨Ruby.fair Y X y g,?_ , fun i U=> Ruby.haloP Y X he' he hy hX i U⟩
   exact hx c N ι β Y X y g p.threshold t he' he hy hX hg hY





end YM.QCD.Kites
