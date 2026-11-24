import YM.Kai.BrightP
import YM.Tinus.SumsR
/-! Linear oblique rates read on total at any stop. Beacon chart sufficient. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast.Rays
variable {u t a D C v e s:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls
variable {S:Scheme}{R:Side}(A:Massive.Run S N R 6)

local notation "S★" i:arg=> S.side R i
variable (g:Site (S.side R m)→Insertion (S.side R m) 6)(u:Sail)(h:i≤ m)
noncomputable def viaP (g:Cover→Insertion (S.side R m) 6)(a:Averaging)(i:ℕ):Insertion (S.side R i) 6:=∑ j:Site (S.side R i), Depth.report A g a i (Lattice.lift j)
include h
lemma scales (v:Averaging)(hv:v=Option.some u): viaP A (fun i=>g (wrap _ i)) v i= ((ratioTo S m i :ℝ)^4)⁻¹ • S.toStop R A.β A.w m i (∑ j:Site (S.side R m),g j):=by
     subst v; unfold viaP report; rw [← map_sum]; have hh:= harmonyR (Hub.viewW S R h) g (odd_to h) u
     rw[show (∑ i':Site (S.side R i),visitor S m i (some u) (lift i') (fun i=>g (wrap _ i)))=((ratioTo S m i:ℝ)^4)⁻¹ • (∑ j,g j) from hh]; exact map_smul ((relay A i).restrictScalars ℝ) _ _ -- grammar
omit h
variable (G:Cover→Insertion (S.side R m) 6)(W:Averaging)(ht:TideT A W m (report A G W))(hA:A.Actual)(hp:i≤ N)
variable (p: Flavor 6)(j t:Fiber)(x y:Axis)(g₀:su.Color)
local notation "φ"=> A.density i
local notation "αᵢ" b:arg=> report A G W i b
local notation "Δ" b:arg=> foil (A.density i) (αᵢ b)
include h ht hA hp
private noncomputable def spot1(a:Axis)(p:Flavor 6)(i j:Fiber): Density c 6→ₗ[ℂ]ℂ:={ toFun:=river1 a p i j,map_add':=fun _ _=>race1 ..,map_smul':=fun _ _=>steps1 .. }
lemma rune (hv:∀ᶠ U':Grid (S★ i) in 𝓝 1, IsUnit (φ U'))(hX: Chart k (Δ 0) 1)(hk:1 ≤ k) :
      river1 y p j t (foil φ (viaP A G W i))=(Fintype.card (Site (S.side R i)):ℂ)*river1 y p j t (Δ 0)∧
      river2 x y p j t g₀ (foil φ (viaP A G W i))=(Fintype.card (Site (S.side R i)):ℂ)*river2 x y p j t g₀ (Δ 0):=by
      let J(x'):=(Δ x'); have he(x:Cover):(φ)=march x φ:=by rw [pier A hA hp]; exact (Patria.Depth.first A i hp x).symm
      have hh(x): march x (αᵢ 0)=⇑(αᵢ x):=(by simpa only [zero_add] using ((ht.moves i h).trans x 0)); have hY(x): J x=ᶠ[𝓝 1] march x (J 0):=by unfold J; rw [← hh]; exact course x _ _ hv (he _).symm
      have hK(x:Cover): Chart k (J x) 1:= frugal _ _ (hY x) (marchC x (J 0) hX); have hz : foil φ (viaP A G W i)= ∑ i':Site (S.side R i),J (Lattice.lift i'):=by funext x; unfold viaP foil; rw [ContinuousMap.sum_apply,mul_sum,Finset.sum_apply]; -- maybe
      rw [hz]; let L₁:=spot1 (c:=S.side R i) y p j t; let L₂:=river2 x y p j t g₀ (c:=S.side R i); have ht(x):L₁ (J x)= L₁ (J 0) := (vote1 _ _ _ _ _ _ (hY x)).trans (march1 (J 0) hX hk ..); have hh'(x'):L₂ (J x')= L₂ (J 0):= (vote2 _ _ _ _ _ _ _ _ (hY x')).trans (march2 (J 0) _ hX hk ..)
      constructor
      · change L₁ _= _ * L₁ (J 0); rw [map_sum]; simp_rw [ht]; rw[sum_const,card_univ,nsmul_eq_mul]
      rw [vote2_sum _ hk _ _ _ _ _ _ univ (fun x _=>hK _)]; change (∑ z:Site (S.side R i), L₂ (J (lift z)))=_ * L₂ (J 0); simp_rw [hh']; rw [sum_const,card_univ,nsmul_eq_mul]
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.rune
#print axioms YM.Massive.Patria.Gall.scales
