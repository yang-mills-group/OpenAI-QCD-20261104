import YM.MassiveQCD.Tangent.Flag
import YM.MassiveQCD.Palette.Taper




/-! # Actual identity readout approximation error
 Includes winding error bound at finite c in the scaled component. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tangent
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove Entr YM.Next.Free Bloch Laurent QCD.Free
open Garden Para Pine Finch AnalyticBridge VerifiedReset Footprint
variable {t s τ u :ℝ}{j k:ℕ}{B:BudgetPoint}
-- control λ leading printed cohort
local notation "K!"=> (Fintype.card (Site c):ℝ)
local notation "S0"=> EvenA c N
open Stew.Phased
variable (b:Flavor N) (E:Gem c N I)
-- main apply to ALL powers 1 stamped. no need rotation. finite volume only assumption. rate invoked later.
lemma sift (h:Licence B u s t E)(hp: ∀ i,Nonwrapping (E.addr i).support (E.addr i).site → Stew.shape (E.addr i).site (meter b (E.view i 1)) none =0)(ht:0<t)(hu:0<u) : t^2 * (c.val * |senseF b (Patron.total E B.threshold 1)|) ≤ Finch.fare u B.B*s:=by
    obtain ⟨z,hz,hZ⟩:=h.zone; let N':=K!; let D:ℝ:=c.val; let R:=Finch.fare u B.B; let α (i:I):=Real.exp (u*(coverNumber B.B (E.addr i).support)); let g i:= z i*α i; let f i:= t^2 * (D*(N'* senseF b (letters E B.threshold 1 i))); have hR: 0 ≤ R:=by unfold R Finch.fare; positivity; -- needs B infer
    have hV : SumBudget g (N'*s):= by
       have h1(i):0≤g i:=mul_nonneg (hZ i).travel (Real.exp_pos _).le
       refine Stem.mast E g ?_ h1 le_rfl (t:=0) (B:=B); intro i; convert hz i using 1; ext j; simp [g,α]
    have hs(i): |f i| ≤ R*g i:=by
       simp only [f,abs_mul,abs_of_nonneg (sq_nonneg t),abs_of_nonneg (show 0≤ N' from Nat.cast_nonneg _),abs_of_nonneg (show 0≤ D from Nat.cast_nonneg _)]
       rw [show letters E B.threshold 1 i=E.view i 1 from masked_eq _ _ _ _ (flat_ok ..)]
       have hL:= rateH E b i ht.le hu (B:=B); have hQ:Stew.lane E b i none=0:= by unfold Stew.lane Stew.mote; split; exact hp i ‹_›; rfl
       dsimp only at hL; rw [hQ,show coz 0=0 from rfl, sub_zero,pStow,norm_mul,Complex.norm_natCast] at hL
       refine le_trans (show _ ≤ t^2*(D * (N' * ‖peel (meter b (E.view i 1)) (0,chad) (0,chad)‖)) from ?_) (hL.trans ?_); · gcongr; exact Complex.abs_re_le_norm _
       exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((hZ i).sizeU _ (flat_ok ..)) (Real.exp_pos _).le) hR
    have hh:= (Lunar.Ring0.absoluteR f (budget_mono (budget_scale hR hV) (fun _=>abs_nonneg _) hs)).2; have hc:0 < N':=by unfold N'; positivity
    rw [show ∑' i,f i=t^2* (D*(N'*senseF b (Patron.total E B.threshold 1))) from (((((senseF b).hasSum (permits _ h ht hu.le 1).hasSum).mul_left N').mul_left D).mul_left (t^2)).tsum_eq] at hh
    simp only [abs_mul,abs_of_nonneg (sq_nonneg t), abs_of_pos hc, abs_of_nonneg (show 0≤ D from Nat.cast_nonneg _)] at hh
    apply le_of_mul_le_mul_left _ hc; change N'* (t^2*(D* _)) ≤ N'*(R*s); linarith only [hh]
end YM.QCD.Tangent
#print axioms YM.QCD.Tangent.sift
