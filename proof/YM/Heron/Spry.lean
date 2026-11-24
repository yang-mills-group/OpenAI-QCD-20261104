import YM.Heron.Mana
import YM.Work.A05.Window
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct DawnS
open Maxwell.Free (exportFlux fromCenter)
open Maxwell (grad away)
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius ComplexOrder
open Finset LinearMap
open UV.Free Tawny Tawny.Cast Tawny.Cast.Carnal Perla Perla.Fore TableT Drill
variable {d:ℕ}(Γ:ℝ→ EuPin)(Δ:Ortho.Skew)(hΓ:EuPin.Path Δ Γ)(b:IceT)(x:Points 2)(hx:x∈conf 2)(χ:E4→ℝ)(hχ:Physics.Window x χ)(p q r: Label d)
local notation "T"=> RawTensor 1 8
local notation "P"=> UV.Free.projection
local notation "R"=> fromCenter Δ.val (x 0)
local notation "S"=> symbS 1
variable (v u:T)(s:IceT→ℂ)
lemma lamp (p q:Label d) : ear x p.val q.val=UV.Free.wick (fun _:Fin 2=>d) x (![p,q]):=by unfold ear UV.Free.wick; rw [MultilinearMap.compLinearMap_apply]; apply congr_arg; funext i;fin_cases i<;>rfl
lemma litEcho (w:Pol d)(y:E4)(hy:Points.cons y x∈conf 3)(i j:Axis)(hv:S u=S v)(hq:P p=P q):trioL y x (![p.val,w]) ((u.val (i,j)).val)= trioL y x (![q.val,w]) ((v.val (i,j)).val):=by
    have hx:x∈conf 2:=by intro i j H; exact Fin.succ_inj.mp (hy (show Points.cons y x i.succ=Points.cons y x j.succ from H))
    rw [trip x y hx hy,trip x y hx hy]; unfold triangle; apply DawnS.descendant _ hy; intro i'; fin_cases i'; exact congr_arg Subtype.val (congr_fun hv (i,j)); exact congr_arg Subtype.val hq; rfl
include hx hχ
lemma purity (w:Pol d)(hv:S u=S v)(hq:P p=P q): plumes x χ Δ u.val p.val w= plumes x χ Δ v.val q.val w:=by
    unfold plumes; apply Maxwell.Free.flux_invariant; intro i y hy; unfold actS; simp_rw [fun j=> litEcho x p q v u w y (torchD x hx y χ hχ hy) i j hv hq]
lemma chara(H: P p=0) :plumes x χ Δ v.val p.val q.val=0:=by rw [purity Δ x hx χ hχ p (0:Label d) v v q.val rfl (by rw [map_zero,H])]; change flower x hx Δ χ hχ v.val (0:Pol d) q.val= 0; rw[map_zero]; rfl
omit hx hχ
variable (σ:RawSym)(Hσ: Hail.RightAuth σ)
include hΓ Hσ
lemma candidate_d (he:P p=0): P (Cane Γ Δ hΓ b d p)=0:=by
    apply Hail.shutD σ _ Hσ; intro v; let x: Points 2:=points (![0,(1:ℝ) • basis timeAxis]); have hx:x∈conf 2:= DawnS.distinct _ zero_lt_one
    obtain ⟨χ,hχ⟩:=Work.A05.has_window x hx
    rw [Hail.wellness,← lamp, ← plunge Γ Δ hΓ b x hx χ (show Physics.Window _ _ from hχ), chara Δ x hx χ hχ p v (yarrow b) he]
omit Hσ
include hx hχ
noncomputable def bendP (s:IceT→ℂ) : RawTensor 1 8 := ∑ i:IceT,s i • yarrow i
lemma loom(hv:S v=S (bendP s)): plumes x χ Δ v.val p.val q.val = ear x (((∑ i:IceT,s i • Cane Γ Δ hΓ i d p):Label d).val) q.val:=by
    let M:= partyR x hx Δ χ hχ p.val q.val; rw [purity Δ x hx χ hχ p p (bendP s) v q.val hv rfl]; change M ((∑ i:IceT,_:T).val)= _; simp only[AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul,_root_.map_sum,_root_.map_smul]; simp_rw [show ∀ b:IceT,M ((yarrow b).val) = ear x (Cane Γ Δ hΓ b d p).val q.val from fun b=> plunge Γ Δ hΓ b x hx χ hχ p q]; obtain ⟨K,h⟩:= bil (d:=d) x; simp only[h,_root_.map_sum,LinearMap.sum_apply,_root_.map_smul,LinearMap.smul_apply]
end YM.Heron
#print axioms YM.Heron.candidate_d
#print axioms YM.Heron.loom
