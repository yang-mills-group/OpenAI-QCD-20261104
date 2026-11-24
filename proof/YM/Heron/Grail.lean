import YM.Heron.Spry
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius ComplexOrder
open LinearMap Finset
open Tawny Tawny.Cast Carnal Perla Perla.Fore TableT Drill
noncomputable def fork (d:ℕ):{ Q:Free.Symbol d→ₗ[ℂ] Label d // projection ∘ₗ Q=LinearMap.id}:= by
     letI : Module.Free ℂ (UV.Free.Symbol d):=Module.Free.of_divisionRing ℂ (UV.Free.Symbol d); let P:= (@projection d); let H':= LinearMap.exists_rightInverse_of_surjective P (LinearMap.range_eq_top.mpr Free.onto); exact ⟨_, H'.choose_spec⟩
variable {d:ℕ}(Γ:ℝ→EuPin)(Δ:Ortho.Skew)(hΓ:EuPin.Path Δ Γ)(b:IceT)
include hΓ
noncomputable def gran (d:ℕ): Module.End ℂ (Free.Symbol d):= projection ∘ₗ Cane Γ Δ hΓ b d ∘ₗ (fork d).val
variable (h:RawSym)(hv:Hail.RightAuth h)(p:Label d)
include hv
lemma joins : gran Γ Δ hΓ b d (projection p)= projection (Cane Γ Δ hΓ b d p):=by
    let P':= (fork d).val (projection p); have he:projection P'=projection p:=DFunLike.congr_fun (fork d).property (projection p); have ht:=(candidate_d Γ Δ hΓ b (P'-p) h hv (by rw[_root_.map_sub UV.Free.projection P' p,he,sub_self])); rw [_root_.map_sub (Cane Γ Δ hΓ b d) P' p, _root_.map_sub UV.Free.projection _ _,sub_eq_zero] at ht; exact ht
lemma taps (κ:IceT→ℂ) (u:Label d) (V:Label d) (hb: projection V = ∑ i:IceT,κ i • gran Γ Δ hΓ i d (projection u))(X:RawTensor 1 8) (ht:symbS 1 X= symbS 1 (bendP κ))(x:Points 2)(hx:x∈conf 2)(χ:E4→ ℝ)(hχ:Physics.Window x χ):
     plumes x χ Δ X.val u.val p.val=UV.Free.wick (fun _:Fin 2=>d) x (![V,p]) :=by
    simp only[fun i:IceT=>joins Γ Δ hΓ i h hv u] at hb; let S:=∑ i:IceT,κ i • Cane Γ Δ hΓ i d u; have hG: projection S=projection V:=by rw[hb]; unfold S; simp only [map_sum,map_smul]
    rw[loom Γ Δ hΓ x hx χ hχ u p X κ ht,lamp]; refine DawnS.trails x hx _ _ ?_; intro i; fin_cases i; exact hG; exact rfl
omit hv hΓ
lemma whale : Hail.flood (-1) (fun _=>-1)= bendP (fun _=>1):=by
      unfold Hail.flood bendP; simp only[one_smul,Fintype.sum_option, yarrow]; change _= -solid+ (∑ i:Flavor 6,_); simp [smul_smul]
lemma magic (i j:Axis): let X:=bendP (fun _=>1); (X.val (i,j)).val= -UV.totalStress i j:=by
    intro X; unfold X; rw [←whale]; unfold Hail.flood; simp only [Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,AddSubmonoidClass.coe_finsetSum,Finset.sum_apply]; rw [gauge_val]; simp only [W_sun, Submodule.coe_add,amt]; unfold totalStress; simp only [neg_one_smul, ← Finset.smul_sum, Finset.sum_neg_distrib, Finset.smul_sum]; abel
end YM.Heron
#print axioms YM.Heron.gran
#print axioms YM.Heron.taps
#print axioms YM.Heron.magic
