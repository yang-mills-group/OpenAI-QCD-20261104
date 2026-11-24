import YM.Lobo.Pike
import YM.Lobo.Tyre
set_option maxHeartbeats 670000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open StressFlux (pair curl0)
open Finset
variable {d:ℕ} (f r: Flavor 6)(P:Bundle)(G: EuPin)(p:PClan)(M Z:Spike)
set_option quotPrecheck false
local notation "L"=>wave (p f).matrix.val
local notation "R"=>wave (p r).matrix⁻¹.val
local notation "R₀"=>wave (p f).matrix⁻¹.val
lemma echoS(d:ℕ) : spun p d (Oriole.coat (fieldB f r (0:Multi d) 0 P))= Oriole.coat (fieldB f r (0:Multi d) 0 (L*(P*R))):=by rw [rollsK]; simp only [mar]; simp [ite_smul]
lemma echoP(a:Axis) : spun p _ (Oriole.coat (fieldB f r (UV.first a) 0 P))= ∑ i:Axis, (↑((p f).coord.val i a):ℂ) • Oriole.coat (fieldB f r (UV.first i) 0 (L*(P*R))):=by
     rw[rollsK]; simp_rw [mar]; simp only [mul_ite,mul_one,mul_zero,ite_smul,zero_smul,sum_ite_eq', mem_univ,↓reduceIte]; exact lift_on ..
lemma echoA(a:Axis) : spun p _ (Oriole.coat (fieldB f r 0 (UV.first a) P))= ∑ i:Axis,(↑((p r).coord.val i a):ℂ) • Oriole.coat (fieldB f r 0 (UV.first i) (L*(P*R))):=by
     rw[rollsK]; rw[sum_comm]; simp_rw [mar]; simp only [ite_mul,one_mul,zero_mul,ite_smul,zero_smul,sum_ite_eq', mem_univ,↓reduceIte]; exact lift_on ..
noncomputable def Euv (p:PClan)(f r:Flavor 6)(x:Spike):= (p f).matrix.val*(x*(p r).matrix⁻¹.val)
lemma pulse : L*(wave M *R)= wave (Euv p f r M):=by rw [wave_mul,wave_mul]; rfl -- orientation
lemma curb(z:su.Color): L*(whirl z M*R₀)= whirl z (conjug (p f) M):=by
     rw[←mul_assoc]; have h:= BendR.poker (p f) (1:ℂ) z M; rwa [one_smul,one_smul] at h
lemma carrying (d:ℕ)(g:SpinPol d) : carr (G,p) d ((1:GPol)⊗ₜ[ℂ] g)=1⊗ₜ[ℂ]spun p d g:=by unfold carr; rw [TensorProduct.map_tmul]; simp
include G
lemma sig0 (d:ℕ) : carr (G,p) _ (bilinear f r M (0:Multi d) 0)= bilinear f r (Euv p f r M) (0:Multi d) 0:=by
    rw [← j_stard]; change carr _ _ ((1:GPol)⊗ₜ[ℂ] Oriole.coat _)=_; rw [carrying,echoS,pulse,← j_stard]; rfl
lemma sigP(a:Axis) : carr (G,p) _ (bilinear f r M (UV.first a) 0)= ∑ i:Axis,(↑((p f).coord.val i a):ℂ) • bilinear f r (Euv p f r M) (UV.first i) 0:=by
    rw[← j_stard]; change carr _ _ ((1:GPol)⊗ₜ[ℂ] Oriole.coat _)=_; rw [carrying,echoP,pulse,TensorProduct.tmul_sum]; apply sum_congr rfl; intro _ _; rw [tmul_smul,← j_stard]; rfl
lemma sigA(a:Axis): carr (G,p) _ (bilinear f r M 0 (UV.first a))= ∑ i:Axis,(↑((p r).coord.val i a):ℂ) • bilinear f r (Euv p f r M) 0 (UV.first i):=by
    rw[← j_stard]; change carr _ _ ((1:GPol)⊗ₜ[ℂ] Oriole.coat _)=_; rw [carrying,echoA,pulse,TensorProduct.tmul_sum]; apply sum_congr rfl; intro _ _; rw [tmul_smul,← j_stard]; rfl
lemma wizard (i j:Axis): putH (G,p) _ (med f i j M) = ∑ a:Axis,∑ b:Axis,(↑(G.coord.val a i*G.coord.val b j):ℂ) • med f a b (conjug (p f) M):=by
     apply Subtype.ext; apply Poised.Display.distinct; intro J; change Poised.Display.ready 10 J (carr (G,p) 10 (youthL f i j M))= _; rw[view,yMobi]; change spun _ 10 (Oriole.coat (fieldB f f (0:Multi 10) 0 (whirl _ M)))=_; rw [echoS,curb]; simp_rw [AddSubmonoidClass.coe_finsetSum,map_sum]; let u:=J 0; let X':=conjug (p f) M; let w:su.Color→ₗ[ℝ]Bundle:= ⟨⟨fun x=> whirl x X', fun x y=>by unfold whirl BendR.ore; rw[map_add]; exact Matrix.kronecker_add X' (BendR.ore x) (BendR.ore y)⟩,fun r x=> by ext i j; simp only[whirl,Matrix.kroneckerMap_apply]; rw[show BendR.ore (r • x)= r • BendR.ore x from su.colorMat.map_smul _ _, Matrix.smul_apply, Matrix.smul_apply]; exact mul_smul_comm ..⟩
     let F:= (Oriole.coat (A:=SpinMode 10)).restrictScalars ℝ
     change F (((yard f).restrictScalars ℝ) (w (curl0 i j (Labels.Taylor.turn G.coord⁻¹ (J 0)))))=_; rw[curlS]; simp_rw [map_sum]; refine sum_congr rfl fun a _=>sum_congr rfl fun b _=>?_ ; rw [map_smul,map_smul, F.map_smul,Submodule.coe_smul, map_smul]; refine congr_arg (fun t:SpinPol 10 => (↑(G.coord.val a i*G.coord.val b j):ℂ) • t) ((yMobi f a b X' J).symm)
end YM.Lobo
#print axioms YM.Lobo.wizard
#print axioms YM.Lobo.sigA
#print axioms YM.Lobo.sig0
#print axioms YM.Lobo.sigP
