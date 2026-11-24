import YM.Gall.Cream
import YM.Tawny.Fore
/-! Exact gauge B read from ANY native payment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised.Stative
open Poised Poised.Display Poised.Beacon PCAC Push.Local Rudder QCD.Kit
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p w:ℕ}
local notation "V₀" => Grid c
local notation "X₀" => Directions su c
local notation "G₀" => Lat.Fields c 6
variable (g:su.Color)
local notation "Y★"=> Cray c
local notation "cv"=> kiln g
local notation "K"=> ink g
variable {A B:Type*} [Fintype A][Fintype B]
open Tawny Cast.Perla Fore
noncomputable def oneT (Y:Alg A):= coef ∅ Y
lemma flat0 (X Y: Matrix A B ℂ)(x: Dirac A) : oneT (adapter X Y x)=oneT x:=by
          unfold oneT; rw [← write x]; simp only [map_sum,map_smul]; refine sum_congr rfl (fun i _ => ?_)
          by_cases h : i=∅
          · subst i; rw [mono_empty,map_one]; rw [show coef (∅:Finset (Pairs A)) 1=1 from TorusPCAC.Ward.zeroR_one,show coef (∅:Finset (Pairs B)) 1=1 from TorusPCAC.Ward.zeroR_one]
          rw [show coef _ (adapter X Y (mono i))=0 from spectrum (Grass.exterior_layer _ (Grass.homogeneous i)) ∅ (fun e=> h (by rw [← Finset.card_eq_zero]; exact e.symm)),show coef ∅ (mono i)=0 from Grass.read_other _ _ (Ne.symm h)]
variable (T:TaperHol)(X:Labels.Taylor su 0)(Y:Labels.Taylor su 1)
lemma f_bane (J:Labels.Jet su)(v:UV.Pol d) : oneT (ready d J v)= Labels.read J (fog v):=by
    unfold oneT; induction v using TensorProduct.induction_on with
    | zero=> rw [map_zero,map_zero,map_zero,map_zero]
    | tmul a b=> rw [ready_t,map_smul,Display.apart,map_smul]; simp only[smul_eq_mul]; ring
    | add a b ia ib=> rw [map_add,map_add,map_add,map_add,ia,ib]
lemma charge (z:ℝ)(t:UV.Label d) (J:Labels.Jet su): oneT (desired t.val J z)= pages (scaleJet J (z^2)) t:=by rw [← observe]; unfold observation; rw [LinearMap.comp_apply]; unfold endor; rw [AlgHom.toLinearMap_apply,flat0,f_bane]; rfl
noncomputable abbrev shrub {c:Side}(F:Density c 6):Grid c→ℂ:= oneT ∘ F
noncomputable abbrev trade (F:Density c 6)(g:su.Color):= crown (shrub F ∘ kiln g)
lemma one_price {A:Type*}[Fintype A](x:Alg A): ‖oneT x‖≤ ‖x‖:=by unfold oneT; rw [Grass.norm_def]; exact single_le_sum (s:=Finset.univ) (f:=fun i:Finset A=> ‖coef i x‖) (fun _ _=>norm_nonneg _) (mem_univ _)
lemma quirky (F:Density c 6)(H:∀ k U,slots 6 k (F (Lattice.gauge k U))=F U): GaugeInvariant (shrub F):=by intro k U; change oneT (F (Lattice.gauge k U))=oneT (F U); rw [←H k U]; exact (flat0 (rotates 6 k) (star (rotates 6 k)).transpose (F (Lattice.gauge k U))).symm
lemma shrub_p (F:Density c 6)(hT: Chart n F 1): Chart n (shrub F) 1:=(((coef (∅:Finset (Pairs (Modes c 6)))).toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt).comp _ hT -- Keys namespace
variable (P F:Density c 6)(Q:UV.Label d)(h:Tally T 0 Q P F)
local notation "f★"=> shrub (Canvas.foil P F) ∘ cv
local notation "J★"=> leanY X Y
local notation "L"=> fling g T.T
include h
lemma relic (hX:Along g X)(hY:Along g Y)(hm: Chart d (Canvas.foil P F) 1)(hd:6 ≤ d)(hk:k ≤ d)(hk':k < 12) : iteratedDeriv k (fun t:ℝ=> pages (scaleJet (leanY X Y) (t^2)) Q) 0=(k.factorial:ℝ) • coin f★ (L X) (L Y) k:=by
    let S:= T.test d P F J★; let W:= desired Q.val J★; let M:= f★; let Y':ℝ → Cray c:=river (L X) (L Y)
    let Z: SpinPol d→L[ℝ]ℂ:=(coef (∅:Finset (Pairs (SpinMode d)))).toContinuousLinearMap.restrictScalars ℝ
    have he : Z ∘ S= M ∘ Y':=by funext i; change oneT (adapter (T.T.spin (d:=d) i) (T.T.spin i) (Canvas.foil P F (T.links c d _ i)))=_; rw [flat0,kicks g T X Y _ hX hY hd]; rfl
    have hZ: Z ∘ W=(fun t:ℝ=> pages (scaleJet J★ (t^2)) Q):= funext fun x=> charge x Q _
    have hb:= (stamps h J★).2; change SourceRead.Agrees S W at hb
    rw [←hZ, Display.clm_step W k _ (hb.2.1.of_le (Nat.cast_le.mpr hk)), ←hb.2.2 k hk, ←Display.clm_step S k _ (hb.1.of_le (Nat.cast_le.mpr hk)),he]; apply money M (k:=d) _ (by omega) _ _ hk hk'; exact collinear g 0 (shrub _) (by rw [kiln0]; exact shrub_p _ hm)
lemma horn8 (hX:Along g X)(hY:Along g Y)(hm: Chart d (Canvas.foil P F) 1)(hd:8 ≤ d) : iteratedDeriv 8 (fun t:ℝ=> pages (scaleJet (leanY X Y) (t^2)) Q) 0=(Nat.factorial 8:ℝ) • ((1/2:ℝ) • trade (Canvas.foil P F) g (L X) (L X)):=by simpa only [coin,if_pos rfl,if_neg (by decide : ¬ (8:ℕ)=0),if_neg (by decide : ¬ (8:ℕ)=4),if_neg (by decide : ¬ (8:ℕ)=6),if_neg (by decide : ¬ (8:ℕ)=10),add_zero,zero_add, if_true] using relic g T X Y P F Q h hX hY hm (by omega) hd (by decide)
lemma horn10 (hX:Along g X)(hY:Along g Y)(hm: Chart d (Canvas.foil P F) 1)(hd:10 ≤ d) : iteratedDeriv 10 (fun t:ℝ=>pages (scaleJet (leanY X Y) (t^2)) Q) 0=(Nat.factorial 10:ℝ) • trade (Canvas.foil P F) g (L X) (L Y):=by simpa only [coin,if_pos rfl,if_neg (by decide : ¬ (10:ℕ)=0),if_neg (by decide : ¬ (10:ℕ)=4),if_neg (by decide : ¬ (10:ℕ)=6),if_neg (by decide : ¬ (10:ℕ)=8),add_zero,zero_add, if_true] using relic g T X Y P F Q h hX hY hm (by omega) hd (by decide)
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.horn10
