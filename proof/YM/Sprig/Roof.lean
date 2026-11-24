import YM.Sprig.Value
/-!
  Positive invariant Hilbert form for discrete ensemble symmetries on Label d. Enforce the normalization later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig.Chloe
open Massive Function Filter Matrix Set Finset QCD QCD.Lat QCD.Grass QCD.Creek Lattice Wilson MeasureTheory
open scoped BigOperators Topology Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ComplexOrder Kronecker
variable {A: Massive.Sequence}(P: Calibration A) {n:Side} {d:ℕ}
open UV Cylinder Patria Patria.Depth
open Patria.Exposure
variable (n:Side)(x y: Label d)
noncomputable def costH (x y: Label d)(U:Grid n):= poly (P.candidate d n 0 x U) (P.candidate d n 0 y U)
local notation "π"=> prior su n
noncomputable def pollen (x y:Label d):ℂ:= ∫ U,(costH P n x y U) ∂(prior su n)
lemma lightH :Continuous (costH P n x y):=by
     unfold costH Chloe.poly; fun_prop -- continuousMap
lemma earnH : Integrable (costH P n x y) π:= (lightH P n x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)
-- Fee
lemma sparks(x y:Label d):star (pollen P n x y)=pollen P n y x:=by
     change ((starRingEnd ℂ) _)=_
     unfold pollen; rw [← integral_conj]; exact integral_congr_ae (Eventually.of_forall fun i=> sun ..)
lemma timely(x y z:Label d):pollen P n (x+y) z=pollen P n x z+pollen P n y z:=by
     unfold pollen; rw [show costH P n (x+y) z=costH P n x z+ costH P n y z from ?_]; exact integral_add (earnH P n x z) (earnH P n y z) -- Map.Algebra
     funext i; unfold costH; rw [map_add]; exact lumenL ..
lemma money(t:ℂ)(x y:Label d):pollen P n (t • x) y= star t * pollen P n x y:=by
     unfold pollen; rw [show costH P n (t • x) y=(star t) • costH P n x y from ?_]; change (∫ i,(star t) • costH P n x y i ∂π)=_; rw[integral_smul]; rfl
     funext i; unfold costH; rw [map_smul]; exact senseL ..
lemma pp0(x: Label d):0 ≤ (pollen P n x x).re:=by change _ ≤ RCLike.re (pollen P n x x); unfold pollen; rw [← integral_re (earnH P n x x)]; exact integral_nonneg fun i=>(Complex.nonneg_iff.mp (posH _)).1
lemma ppU(x:Label d)(hp:Injective (P.candidate d n 0))(hx:x ≠0) :0 < (pollen P n x x).re:=by
     haveI:(prior su n).IsOpenPosMeasure:=by unfold prior; infer_instance
     change _ < RCLike.re (pollen P n x x); unfold pollen; rw [← integral_re (earnH P n x x)]; let g:= fun i:Grid n=> (costH P n x x i).re; have ht:Continuous g:=Complex.continuous_re.comp (lightH P n x x)
     have hh: ∃ U: Grid n,P.candidate d n 0 x U≠0:=by by_contra! h; exact hx (hp ((ContinuousMap.ext (g:=0) (fun U=> h U)).trans (map_zero _).symm)) -- implicit g
     obtain ⟨U,hU⟩:=hh; exact (integral_pos_iff_support_of_nonneg (f:=g) (fun i=>(Complex.nonneg_iff.mp (posH _)).1) (ht.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..))).mpr ((isOpen_ne_fun ht continuous_const).measure_pos _ ⟨U,(Complex.pos_iff.mp (onlyH _ hU)).1.ne'⟩) -- pos_iff sign
variable (h: P.System)
variable {Y : Type*}
open TorusPCAC.Geometry TorusPCAC.Geometry.AxisB TorusPCAC.Geometry.Switch TorusPCAC.Ward TorusPCAC.Jet TorusPCAC.Jet.Selector QCD.Revolve
lemma frameC : Jobs n 6 Cmat ∈ unitary _:=by
    let X:= Jobs n 6 Cmat
    have he: star X=Jobs n 6 Cmat⁻¹:=by
         have hx:star Cmat=Cmat⁻¹:=by rw [inverse_C]; unfold Cmat; rw [star_mul,gamma_star, gamma_star]
         exact (drum Cmat).trans (congr_arg (Jobs n 6) hx)
    constructor
    · apply Eq.mp _ (pay Cmat Cmat⁻¹ (N:=6) (n:=n) pays_C); change _=(star X*X=1); rw[he]
    rw [show star (Jobs n 6 Cmat)= Jobs n 6 Cmat⁻¹ from he]; exact pay _ _ pays_C'
#print axioms frameC

end YM.Sprig.Chloe
#print axioms YM.Sprig.Chloe.ppU
#print axioms YM.Sprig.Chloe.frameC
