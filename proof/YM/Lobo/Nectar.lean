import YM.Lobo.Mix
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole UV.Free Iceberg
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Finset
open scoped YM.Massive.Poised.Plans.Stamp
variable (f:Flavor 6)(k i j:Tri)(w:Bool) (p:RawSym)(s:Hail.RightAuth p)(z:IceT→ℝ)
include s
lemma atW : omegaQ k z 10 (projection (rente f i))= (z none:ℂ) • (drive k (fun a=> projection (rente f a)) i):=by
     unfold omegaQ reachΩ; simp_rw[LinearMap.sum_apply,LinearMap.smul_apply,fun c:IceT=> joins (pathW k) (Omega k) (treks k) c p s (rente f i), fun c=> ruin f k i c]; rw [sum_eq_single (none: IceT)]; · rw [if_pos rfl]; unfold drive; simp only[_root_.map_sum,map_smul]
     · intro v _ h; rw [if_neg h,map_zero,smul_zero]
     simp
lemma omega_non (u:IceT)(h:z u ≠0): omegaQ k z 10 ≠0:=by
     intro he
     cases u with
     | none=>
          let F:Flavor 6:= 0; have H:=truss F k (edgeK k) k p s z; have hz:(z none:ℂ)≠0:= by exact_mod_cast h
          rw [he, LinearMap.zero_apply,gammaE k, gammaY k,smul_zero,add_zero] at H; exact raysM F (lieu k) (backK k) ((smul_eq_zero.mp H.symm).resolve_left hz)
     | some i=>
          have H:=truss i k k (edgeK k) p s z; have hz:(z (some i):ℂ)≠0:=by exact_mod_cast h
          rw [he,LinearMap.zero_apply,gammaE k,gammaY k,smul_zero,zero_add] at H; exact raysM i _ k ((smul_eq_zero.mp H.symm).resolve_left hz)
end YM.Lobo
#print axioms YM.Lobo.omega_non
#print axioms YM.Lobo.atW
