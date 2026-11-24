import YM.QCD.Finch.Offer
import YM.QCD.Stem.Arc
import YM.QCD.Lunar.Photon
import YM.MassiveQCD.Palette.Lamp
/-! # Offset marker projection from the ACTUAL total coefficient
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
-- avoid Nat casts errors
noncomputable def fanF (c:Side): Sheet c→L[ℂ]ℂ:=LinearMap.toContinuousLinearMap {
   toFun:= fun x=>peel x (0,chad) (0,chad)
   map_add':= fun x y=>by rw [peel_add]; rfl
   map_smul':=fun c x=> by rw [peel_smul]; rfl }
noncomputable def senseF (b:Flavor N):EvenA c N→L[ℝ]ℝ:= Complex.reCLM.comp (((fanF c).comp (meter b)).restrictScalars ℝ)
local notation "K!"=> (Fintype.card (Site c):ℝ)
local notation "S0"=> EvenA c N
variable (b:Flavor N) (E:Gem c N I)
lemma sizeF (i:S0)(h:0≤t)(x:Site c): t^2*(K! * |senseF b i|) ≤ Sen x t i:=by
    have hk:= (mw x b i h).1; rw [pStow,norm_mul,Complex.norm_natCast] at hk
    apply le_trans _ hk; gcongr -- gcongr direction? need sense defeq
    exact Complex.abs_re_le_norm _
lemma shelf (M:Sheet c):flagW M=(fanF c M).re:=rfl
lemma pardon (i:S0):senseF b i=flagW (meter b i):=rfl
lemma finger (h:Licence B u s t E)(ht:0<t)(hu:0 ≤ u) : t^2 * |senseF b (Patron.total E B.threshold 1)| ≤ s:=by
    obtain ⟨z,hz,hZ⟩:=h.zone; let N':=K!; let f i:= t^2 * (N'* senseF b (letters E B.threshold 1 i)); have hV : SumBudget z (N'*s):= Stem.mast E z hz (fun i=>(hZ i).travel) hu; have hp(i): |f i| ≤ z i:= by
       simp only [f,abs_mul,abs_of_nonneg (sq_nonneg t),abs_of_nonneg (show 0≤ N' from Nat.cast_nonneg _)]
       rw [show letters E B.threshold 1 i=E.view i 1 from masked_eq _ _ _ _ (flat_ok ..)]
       have hr:= sizeF b (E.view i 1) ht.le (E.addr i).site; exact hr.trans ((hZ i).sizeU _ (flat_ok ..))
    have hh:= (Lunar.Ring0.absoluteR f (budget_mono hV (fun _=>abs_nonneg _) hp)).2; have hc:0 < N':=by unfold N'; positivity
    rw [show ∑' i,f i=t^2* (N'*senseF b (Patron.total E B.threshold 1)) from ((((senseF b).hasSum (permits _ h ht hu 1).hasSum).mul_left N').mul_left (t^2)).tsum_eq, abs_mul,abs_mul,abs_of_nonneg (sq_nonneg t),abs_of_pos hc] at hh; apply le_of_mul_le_mul_left _ hc; rwa [mul_left_comm]
lemma ses (z:Flavor N→ℝ) (B:BudgetPoint): senseF b (Patron.total (Stew.Phased.canon c z) B.threshold (1: Grid c))=z b:=by -- remove m U
    unfold Patron.total; rw [tsum_fintype,pardon,map_sum]; let G:=Stew.Phased.canon c z; have he i : meter b (letters G B.threshold 1 i)=Stew.localX i ((z b:ℂ) • 1):=by rw [show letters G _ _ _= G.view i 1 from masked_eq _ _ _ _ (flat_ok ..)]; exact Stew.Phased.tidyF _ _
    change flagW (∑ i,meter b (letters G _ (1:Grid c) i))=_; simp_rw [he,pineS]
    rw [← Finset.smul_sum,volley,on_spin_one]; unfold flagW; rw [peel_smul,peel_one]; simp

end YM.QCD.Tangent
#print axioms YM.QCD.Tangent.finger
