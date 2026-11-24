import YM.Heron.Barb
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Arise.Range
open Maxwell.Free (exportFlux fromCenter)
open Maxwell (grad away)
open Finset
variable {d:ℕ}(x:Points 2)(hx:x∈conf 2)(χ:E4→ℝ)(hχ:Massive.Physics.Window x χ)(u:Flavor 6)(Γ:ℝ→EuPin)(Δ:Ortho.Skew)(hΓ:EuPin.Path Δ Γ)(R S:List (letters d))(U: List (Dot d) → ℂ)
local notation "W"=> tot R S
noncomputable abbrev dualD {β:Type*}(u:List β)(f:β→β→List β→ℂ):ℂ:= slips u (fun i l=> slips l (fun j m=> f i j m)) -- add variable
local notation "E"=> combD x Δ u
local notation "Y"=> charm x Γ u
include hx hχ hΓ
private theorem vanishK(c d':Dot d)(h:c.1=d'.1): Y c d'=0:=by
      unfold charm; split; swap; rfl
      rename_i hc; obtain ⟨a,v⟩:=c; obtain ⟨b,w⟩:=d'; dsimp only at hc h; subst b a; obtain ⟨t,p,i,k,v,rfl⟩:= voicing v; change dawd x (0,w) _= _; by_cases he:v=u; subst v; exact hazeY x hx u Γ Δ hΓ p i k t w; exact sunny x v u Γ Δ hΓ p i k t (Ne.symm he) _ -- explicit
lemma paid : dualD W (fun i j w=> combD x Δ u i j χ*U w) = 4* slips R (fun b r=> slips (tot r S) (fun j w=> charm x Γ u (0,b) j * U w)) :=by
     let V:= fun (i j:Dot d)(w:List (Dot d))=>combD x Δ u i j χ *U w
     let F:= fun (i j:Dot d)(w:List (Dot d))=>if i.1=(0:Fin 2) then V i j w else 0
     let G:=fun (i j:Dot d)(w:List (Dot d))=> if i.1=(0:Fin 2) then 0 else V i j w
     have h (L:List (Dot d)): dualD L V=dualD L F+dualD L G:=by
           rw [show V=F+G from (funext (fun i=>funext fun j=>funext fun l=>by unfold F G; simp only [Pi.add_apply]; split_ifs<;>simp))]; unfold dualD slips; simp only [Pi.add_apply,smul_add,sum_add_distrib]
     -- change G reversed. Terms with B slot2&A slot2 vanish.
     let Z:= fun (i j:Dot d)(w:List (Dot d))=> 4* charm x Γ u i j * U w
     have he(i j:Dot d)(w:List (Dot d)): F i j w-G j i w = Z i j w:=by
          obtain ⟨i,c⟩:=i; obtain ⟨j,v⟩:=j; have ht:= stuck (d:=d) x hx χ hχ u Δ; have hf:= vanishK x hx χ hχ u Γ Δ hΓ (d:=d); have hp:= arcs x hx χ hχ u Γ Δ hΓ c v
          unfold F G V Z; dsimp only; have hi:i=0∨i=1:=by omega
          have hj:j=0∨j=1:=by omega
          rcases hi with hi|hi <;> rcases hj with hj|hj <;> subst i <;> subst j
          · rw [if_pos rfl, if_pos rfl,sub_zero, ht (0:Fin 2), hf (0,c) (0,v) rfl]; simp
          · rw [if_pos rfl, if_neg (by decide), ← sub_mul, hp]
          ·  simp [charm] -- syntax
          rw [if_neg (by decide),if_neg (by decide),ht (1:Fin 2), hf (1,c) (1,v) rfl]; simp
     change dualD W V=_; rw [show dualD W V=dualD W Z from (?_)]; swap
     · rw [h W]; unfold dualD; rw [slips_twice W G]; unfold slips; simp only [← sub_eq_add_neg,←sum_sub_distrib,←smul_sub,he] -- shape
     unfold dualD tot; rw [slips_append]; unfold joiner; simp_rw [slips_map];
     rw [show (slips S _)=(0:ℂ) from ?_,smul_zero,add_zero]; swap
     · unfold slips; apply sum_eq_zero; intro i _; simp [Z,charm]
     unfold Z slips; simp only[smul_eq_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; try rw [Finset.mul_sum];
     apply sum_congr rfl; intro j _; ring; -- pattern
end YM.Heron
#print axioms YM.Heron.paid
