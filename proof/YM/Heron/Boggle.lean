import YM.Heron.Patch
import YM.Heron.Quad
import YM.Heron.Queen
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct DawnS
open Maxwell Maxwell.Free
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Finset Tawny Tawny.Cast Perla Perla.Fore Carnal
variable {d:ℕ}(x:Points 2)(hx:x∈conf 2)(Γ:ℝ→EuPin)(Δ:Ortho.Skew)(h:EuPin.Path Δ Γ)(χ:E4→ℝ)(hχ:Massive.Physics.Window x χ)(p q:GPol)(u v:List (letters d))

local notation "H"=> Hail.tagD u
local notation "A"=> Hail.tagD v
local notation "P"=> p⊗ₜ[ℂ] Hail.tagD u
local notation "Q"=> q⊗ₜ[ℂ] Hail.tagD v
noncomputable def plumes (x:Points 2)(χ:E4→ℝ)(s:Ortho.Skew)(m:Axis×Axis→ UV.Label 8)(p q:UV.Pol d):ℂ:= Maxwell.Free.exportFlux (actS x s (![p,q]) m) χ
local notation "K"=> plumes x χ Δ
local notation "W"=> tot u v
local notation "U"=> (![Maxwell.reduceEq p, Maxwell.reduceEq q])
local notation "T"=> fiesta x (tot u v)
include hx
lemma grasp : ∃ y:E4, Points.cons y x ∈ conf _:=by -- grammar
     obtain ⟨y,hy⟩:= Infinite.exists_notMem_finset (Finset.image (fun i:Fin 2=>x i) Finset.univ); have he(i:Fin 2) : y ≠ x i:= fun h=> hy (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,h.symm⟩); refine ⟨y,fun i j=>?_⟩
     refine Fin.cases ?_ (fun i=>?_) i; · refine Fin.cases (fun _=>rfl) (fun j=>?_) j; simp[Points.cons,he]
     refine Fin.cases ?_ (fun j=>?_) j; · simp [Points.cons,Ne.symm (he i)]
     simp only[Points.cons,points_apply, Fin.cons_succ]; exact fun hi=> congr_arg Fin.succ ((show Injective x.ofLp from hx) hi)
include hχ h
lemma gust_b(z:QCD.Flavor 6) : HasDerivAt (fun t=> ear x (carr (aPaneB z (Γ t)) d P) Q) (-(1/4:ℂ)* plumes x χ Δ (sunS z).val P Q) 0:=by
   simp_rw [pulse_o]; change HasDerivAt (fun t=> ear x (p⊗ₜ[ℂ] (spiritX z Γ t d (Hail.tagD u))) Q) ((-(1/4:ℂ))* exportFlux (actS x Δ (ballow p q u v) (sunS z).val) χ) 0; obtain ⟨y,hy⟩:=grasp x hx; rw[prices χ x hx hχ];
   have H':=spawnX x hx p q z u Δ Γ h y hy v; rw[paid x hx χ hχ z Γ Δ h u v (fun l=>ester x p q* fiesta x l)] -- expected p args check
   refine HasDerivAt.congr_deriv H' ?_; ring
-- actual gauge
omit hx h hχ
-- prove equals PairStress pol; Maxwell.kr
lemma Maxwellian(i j:Axis): Maxwell.Free.polStress su i j= Maxwell.Free.sheetEnergy i j- (if i=j then (1/4:ℂ) • ∑ k:Axis, Maxwell.Free.sheetEnergy k k else 0):=by unfold Maxwell.Free.polStress; simp_rw [Maxwell.Free.kr_eq]; split_ifs<;>norm_num
lemma graph (i j:Axis) : ∃ g:GPol,(solid.val (i,j)).val = g ⊗ₜ[ℂ]1 ∧ reduceEq g= Maxwell.Free.polStress su i j:=by
    let V(i j:Axis):GPol:= ∑ k:Axis,(StressFlux.pair su i k j k).val; let f:= ∑ k:Axis,V k k; let s:= V i j- (if i=j then (1/4:ℂ) • f else 0); refine ⟨s,?_,?_⟩
    · rw [gauge_val]; unfold s f V gaugeStress; split<;> simp only[← Perla.fullD, show ∀ i j k l,(GG i j k l).val = (StressFlux.pair su i j k l).val⊗ₜ[ℂ]1 from fun _ _ _ _=>rfl,sub_tmul,sum_tmul,sub_zero]; rw[← smul_tmul']; simp only[sum_tmul] -- goal lhs maybe
    rw [Maxwellian]; have he(i j:Axis):reduceEq (V i j) = sheetEnergy i j:=by unfold V; rw [map_sum]; apply sum_congr rfl; intro k _; exact Hail.pairR ..
    unfold s f; rw [map_sub,he]; split; · rw [map_smul,map_sum]; simp only[he]
    rw[map_zero]
include hx hχ
lemma sunup : plumes x χ Δ solid.val P Q= - T * Maxwell.Wick.moment su x (![ Maxwell.Free.rewired (Maxwell.Free.wheel su Δ) (reduceEq p),reduceEq q]):=by
    let s:=stressRead x (fromCenter Δ.val (x 0)) U; have hW:Table.Window x χ:= hχ; have he : exportFlux s χ=-(Maxwell.Wick.moment su x (![ Maxwell.Free.rewired (Maxwell.Free.wheel su Δ) (reduceEq p),reduceEq q])):=by
       refine Eq.trans (moment_force hx hW (rotational_motion hχ.1 hχ.2.1 (lode x hx χ hχ) Δ) U) (?_); apply congr_arg; apply congr_arg; funext i; fin_cases i<;>simp
    unfold plumes; rw [show _= _ from (show exportFlux (actS x Δ (![P,Q]) solid.val) χ = exportFlux (T • s) χ from ?_), valueM, he]; · ring -- smul simpl
    apply Maxwell.Free.flux_invariant; intro i y hy; let Y:=Points.cons y x; have hp:Y∈conf 3:=torchD x hx y χ hχ hy ; let K'(j k:Axis)(y:E4):=fromCenter Δ.val (x 0) k y • Maxwell.Free.bookend x y U (Maxwell.Free.polStress su j k); change (∑ j:Axis, fromCenter Δ.val (x 0) j y • trioL y x (![P,Q]) ((solid.val (i,j)).val))= fiesta x (tot u v) • (∑ j:Axis,K' i j y); rw [Finset.smul_sum]; refine sum_congr rfl fun j _=>?_ ; obtain ⟨g,h,h'⟩:=graph i j; rw [h, build x y hx hp]; unfold K'; rw[book_eval,h']; rw [show twig (hill d) 0 (1:SpinPol 8)=1 from map_one _,one_mul,auxili x y hx hp]; change _ • (Maxwell.Wick.moment su Y _ * T) = T * (_ • Maxwell.Wick.moment su Y _); rw [mul_comm _ T, ← mul_smul_comm]; rfl -- direction check
include h
lemma spaceDance : HasDerivAt (fun t=> ear x (carr (bPaneB (Γ t)) d P) Q) (-plumes x χ Δ solid.val P Q) 0:=by
    obtain ⟨y,hy⟩:=grasp x hx; simp_rw [pulse_blue, seedG x y hx hy]; rw [sunup x hx Δ χ hχ]; simp_rw [wreath,h.2.2, ← Hail.sense]; let F:= (LinearMap.flip (Hail.canopy x)) (Maxwell.reduceEq q); refine HasDerivAt.congr_deriv ((paintsL Δ (Maxwell.reduceEq p) F).mul_const T) ?_; change _ *_= -(-_*_); rw[neg_mul,neg_neg,mul_comm]; rfl
end YM.Heron
#print axioms YM.Heron.gust_b
#print axioms YM.Heron.sunup
