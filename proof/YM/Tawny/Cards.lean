import YM.Tawny.Sheer
import YM.Tawny.Boom
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Drill
open TableT Carnal Rays Perla Zinc Perla.Fore Dream Dream.Clove
open scoped Kronecker
variable (v:Axis→ℂ)(b' c: Hue)(i j k:Axis)(M:Spike)(f g: Pinor →ℂ)(h:SlashV v f) (X:Maxwell.TaylorTower su) (S: Spike)
variable {I:Type}
local notation "PX"=> UV.Free.projection
noncomputable def symbI (Q:Submodule ℂ (I→Label d)): Q→ₗ[ℂ](I→ UV.Free.Symbol d):= LinearMap.pi fun i=> projection ∘ₗ LinearMap.proj i ∘ₗ Q.subtype
noncomputable abbrev symbS(e:ℂ):= @symbI 8 (Axis×Axis) (RawTensor e 8) -- args inspect
noncomputable abbrev symbV:= @symbI 10 Axis (RawVec 10)
noncomputable def quoS := (symbS 1) ∘ₗ poseσ
noncomputable def quoA := (symbS (-1)) ∘ₗ poseα
noncomputable def quoV:= symbV ∘ₗ plaza
noncomputable def vitaT(X:Label d) : ℂ:= vitality a v b' c f g h (0:Maxwell.TaylorTower su) d X.val
local notation "Ψ"=> vitality a v b' c f g h X
local notation "Ω"=>goldF a v b' c f g h X
-- avoid Prop D: image. derive component equations
include h
lemma conveys {x y:Label d}(ht:PX x=PX y): Ψ d x.val=Ψ d y.val∧Ω d x.val=Ω d y.val:=by
    have hu:=congr_arg Subtype.val ht; unfold vitality goldF; change reduceEq x.val=reduceEq y.val at hu; simp only [LinearMap.comp_apply,hu,and_self]
lemma shine_e : Ω 10 ((leapV.val i).val)=pages (lexY X) (leapV.val i)∧ Ω 10 (lunar.val i).val=pages (lexY X) (lunar.val i):=by
    rw [oleap,olun]; constructor
    · rw [map_sum]; -- on LHS fails if rewrite coer; general simp
      simp only [AddSubmonoidClass.coe_finsetSum,map_sum]; exact sum_congr rfl fun i _=> Eq.trans (axisU ..) ((railX _ _ _ rfl).symm)
    simp_rw[AddSubmonoidClass.coe_finsetSum,map_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; exact Eq.trans (axisU ..) ((railX _ _ _ rfl).symm)
lemma meter_v : Ψ 10 (leapV.val i).val=0 ∧ Ψ 10 (lunar.val i).val=0∧ Ψ 10 (eulerV.val i).val=0:=by
    rw [oleap,olun,oeul]; simp only [AddSubmonoidClass.coe_finsetSum,map_sum, show ∀ l i j k u, Ψ 10 (GE l i j k u).val=0 from fun _ _ _ _ _=> visaU ..,sum_const_zero,and_self]
lemma meter_s : Ψ 8 (epi.val (i,j)).val=0 ∧ Ψ 8 (spire.val (i,j)).val=0∧ Ψ 8 (shadow.val (i,j)).val=0∧ Ψ 8 (eclipse.val (i,j)).val=0:=by
     rw [epi_at, spire_val,shadow_val, dark]; split_ifs <;> simp only [show Ψ 8 (UV.unit 8)=0 from visaU ..,AddSubmonoidClass.coe_finsetSum,Submodule.coe_zero,map_sum,show ∀ i j k l, Ψ 8 (GG i j k l).val=0 from fun _ _ _ _=> visaU ..,sum_const_zero,and_self,map_zero]
lemma unplug {d:ℕ}(p:Label d)(hP:p.val=plain d (fog p.val)): Ω d p.val=pages (lexY X) p:=by nth_rw 1[hP,axisU]; rfl
lemma bio(i j k l:Axis): Ω 8 (GG i j k l).val=pages (lexY X) (GG i j k l):= unplug a v b' c f g h X _ (by rw [grit]; rfl)
lemma shine_S (x:Fin 4→ℂ): Ω 8 ((gaugeσ x).val (i,j)).val=pages (lexY X) ((gaugeσ x).val (i,j)):=by
     have he : Ω 8 (epi.val (i,j)).val=pages (lexY X) (epi.val (i,j)):=by rw[epi_at,plotA]; split; exact (axisU a v b' c f g h X (1:GPol)).trans (map_one _); exact map_zero _
     have ht(i):Ω 8 (shadow.val (i,i)).val=pages (lexY X) (shadow.val (i,i)):=by
          rw [shadow_val, if_pos rfl, AddSubmonoidClass.coe_finsetSum,map_sum,map_sum]; exact sum_congr rfl fun _ _=>bio a v b' c f g h X _ _ _ _
     simp only[gaugeσ,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,he,spire_val,dark,shadow_val]; split_ifs <;> simp only[AddSubmonoidClass.coe_finsetSum, Submodule.coe_zero,map_zero,map_sum,bio]
omit h
lemma simplify_s : symbS 1 (traceT a) = 0:= funext fun ⟨i,j⟩=>oppH ..
lemma simplify_a : symbS (-1) (arcS a) = -symbS (-1) (windS a):=by
    funext ⟨i,j⟩; change projection ((arcS a).val _) = -projection ((windS a).val _); refine eq_neg_of_add_eq_zero_left (G:=UV.Free.Symbol 8) ?_; change projection ((arcS a).val _)+projection ((windS a).val _)=0; rw [add_comm, ← map_add,oppA]
lemma tax_and : symbV (lapL a)=0 ∧ symbV (beeA a)=0 ∧symbV (slashS a)=0 ∧ symbV (slashT a)=0 ∧ symbV eulerV=0:= ⟨funext fun i=>Dream.tLocus a i,funext fun i=>boo a i,funext fun i=>gust a i,funext fun i=>gradeR a i,funext fun i=>Dream.tOmega i⟩
end Drill
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Drill.shine_S
#print axioms YM.Massive.Tawny.Cast.Drill.tax_and
