import YM.Giles.Rhythm
/-! Functional readout on relative total sources. Telescope exact on DS trials at this trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s σ :ℝ}{c:Side}{n l d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Complex (exp I)
open Tawny Tawny.Cast.Rays
variable (T:TaperHol)(g:su.Color)(F P:Density c 6)(p:Flavor 6)(i j:Fiber)(a b:Axis)
local notation "Q"=> reed p p i j
local notation "Λ"=> (0:Multi 10)
local notation "N"=> ballast Λ Λ T.T
local notation "μ"=> mu2 a T.T
local notation "B"=>touch (su.colorMat g)
local notation "L"=>fling g T.T (legV g a b)
local notation "A"=>foil P F
lemma banner1(a:Axis): scale_e (c:=c) (mu2 a T.T) 1 2∧ scale_e (c:=c) N 1 2:=by
    have hh(x y:Site c): ‖Np T.T x*Np T.T y‖ ≤1:=(norm_mul ..).le.trans (mul_le_one₀ (tintE ..) (norm_nonneg _) (tintE ..))
    constructor
    · intro x y; unfold mu2; rw[norm_mul, Complex.norm_real, norm_neg]; apply (mul_le_of_le_one_right (norm_nonneg _) (hh ..)).trans; rw [one_mul]; exact ((inkL ..).1).trans (le_self_pow₀ (arm ..) (by norm_num))
    intro x y; rw [originX,one_mul]; exact (hh ..).trans (one_le_pow₀ (arm ..))
lemma ceres (X:Label 10)(hA:Chart 10 A 1)(hf:SungP A)(h: Tally T 0 X P F)(he:a≠b)(hp:‖g‖=1) : leaf2 p i j g a b T.T A-awake2 a b p i j g X= Q μ (tent g A (woodG b c))+Q N (tent g A (swapV T.T g a b c)) :=by
     let V:= tent g A; let x:= glaze (rimV a b) (c:=c); let y:=glaze (indexT b (c:=c)); let L': Y★:=L; let z:=monoT (c:=c) b; let p': Y★:=arcT a b; rw [awake2,LinearMap.add_apply,← purseH T g F P p i j a b X h hA hf he,← stood T g F P p i j a b X h (along_leg0 g a b hp) hA]; change _ - (Q μ (V y)+ Q N (V x)+Q N (V L'))=_; change Q μ (V z)+Q N (V p')-_ = Q μ (V (_-_))+ Q N (V (p'-L'-x)); simp_rw [map_sub]; abel
lemma speedT (U:BudgetPoint)(hu:3 ≤ U.power)(he:a≠b)(hh:‖g‖=1):∃ C:ℝ,0 ≤ C∧ ∀ c:Side,∀ (F P:Density c 6)(n:ℕ)(D:ℝ)(Z:Label 10), Allow U g (foil P F) n D→SungP (foil P F)→Tally T 0 Z P F→ 10 ≤ n →∀ p i j, ‖river2 a b p i j g (foil P F)-awake2 a b p i j g Z‖≤ (c.val:ℝ)⁻¹*C*D:=by
     obtain ⟨S,hS,hP⟩:= gleam_h U g a b T (by omega); obtain ⟨W,hW,hQ⟩:= tithe U g _ (nightF T.T b) (by omega); obtain ⟨Y,hY,hV⟩:= tithe U g _ (dawnF T.T g a b he hh) hu; refine ⟨S*(2*Real.pi)+(W+Y),by positivity[Real.pi_pos],fun c F P n D Z h0 hG h1 hn p' i' j'=>?_⟩
     let f:= foil P F; let T':=tent g f; let o:=woodG b c; let Y':= swapV T.T g a b c; let X:= reed p' p' i' j' (ballast (0:Multi 10) (0:Multi 10) T.T) (T' Y'); let R:= reed p' p' i' j' (mu2 a T.T) (T' o); let z:=(c.val:ℝ)⁻¹; have hz:0 ≤ z:=by unfold z; positivity
     have ht(c':Cray c): T' c'= (z:ℂ) • T' ((c.val:ℝ) • c'):=by rw [Complex.coe_smul,←map_smul,smul_smul,show z*(c.val:ℝ)=1 from inv_mul_cancel₀ (by positivity),one_smul]
     have hhP: peaks p' i' j' (T' Y') ≤ z*(Y*D):=by nth_rw 1[ht]; rw [p_scaled,Complex.norm_real,Real.norm_of_nonneg hz]; exact mul_le_mul_of_nonneg_left (hV _ _ _ _ _ _ _ h0) hz
     have hhQ: peaks p' i' j' (T' o) ≤ z*(W*D):=by nth_rw 1 [ht]; rw [p_scaled,Complex.norm_real,Real.norm_of_nonneg hz]; exact mul_le_mul_of_nonneg_left (hQ _ _ _ _ _ _ _ h0) hz
     have h2:=banner1 (c:=c) T a; have hr:‖R+X‖ ≤ z*(W*D)+z*(Y*D):=(norm_add_le ..).trans (add_le_add ((pupils _ p' i' j' hhQ _ h2.1 zero_le_one).trans_eq (one_mul ..)) ((pupils _ p' i' j' hhP _ h2.2 zero_le_one).trans_eq (one_mul ..)))
     let f':=leaf2 p' i' j' g a b T.T f; apply (norm_sub_le_norm_sub_add_norm_sub _ f' _).trans; rw [show f'- awake2 _ _ _ _ _ _ _= _ from ceres T g F P p' i' j' a b Z (h0.alive.of_le (Nat.cast_le.mpr hn)) hG h1 he hh]; exact (add_le_add (hP _ _ _ _ h0 i' j' p') hr).trans_eq (by unfold tick z; ring)
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.speedT
