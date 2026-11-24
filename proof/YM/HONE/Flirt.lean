import YM.HONE.Mills
import YM.Talis.Nectar
/-! # checkE reprinting. Alphabet launch/reflection booster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox QCD.Lat QCD.Grass MassiveQCD MassiveQCD.Cupola
open scoped BigOperators Classical
namespace CardsT
open Column Finset Plum UV
-- exchange units. Observation Wk, Pe.Trace. normalized-horizon template all <Πσ. funding rail budget
lemma colorL {F:ℕ}{r:Side} (T:Cells.Tiling r)(K:Regulator r F)(x:Stud r F)(p:T.Cell)(u:ℝ) : topH T K ((u:ℂ) • x) p= |u| *topH T K x p := by
     let Y:= palmH T x p; let N:=Fintype.card T.Cell; apply le_antisymm
     all_goals refine le_of_pow_le_pow_left₀ (n:=N) (T.cells_positive).ne' ?_ (le_of_eq ?_)
     · exact mul_nonneg (abs_nonneg _) (top_nn ..)
     rotate_left
     · exact top_nn ..
     symm
     all_goals
         have hp : ∀ l:List T.Cell,(l.map (palmH T ((u:ℂ) • x) p)).prod=(u:ℂ)^l.length • (l.map (palmH T x p)).prod:=by
              intro l; induction l with
              | nil=> simp
              | cons a l ih=> simp only [List.map_cons,List.length_cons,List.prod_cons,ih]; change ((palmH T _ p a) * _)= _; rw [show palmH T _ p a= _ from Lyre.road_real _ x u, smul_mul_assoc,mul_smul_comm, pow_succ',mul_smul]; rfl
         rw [show _=_ from (top_power T K p ((u:ℂ) • x)), mul_pow,show _=_ from top_power T K p x,loom,hp,Lyre.spend]; unfold loom; rw[norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,length_toList,card_univ]
-- `hπ` consumed by Pulse norm ratio.E.V.No sal abuse. value convert final.Engine.Word whenever root multiplier validated from Cadence.Real.Trace.
lemma tributeRoot {F:ℕ}{r:Side}(T:Cells.Tiling r)(K:Regulator r F)(x:Stud r F)(p:T.Cell) (G Y u v W:ℝ)(n:ℕ)(hn:n=Fintype.card T.Cell)(ht:0≤G)(hu:0 < u)(hv:0 < v) (hx: 0 < W)(hδ:Y=topH T K x p ^ n)(hV:Y*(u*v*W)^n ≤ (u*v*G)^n): topH T K ((W:ℂ) • x) p ≤ G:=by
     rw [colorL,abs_of_pos hx]; subst Y n
     let n:= Fintype.card T.Cell; let k:=u*v; have h: k*(topH T K x p * W) ≤ k*G:=by
          apply le_of_pow_le_pow_left₀ (Nat.ne_of_gt T.cells_positive) (mul_nonneg (mul_pos hu hv).le ht); change _ ≤ (u*v*G)^n; refine le_trans (le_of_eq ?_) hV; rw[mul_pow _ (topH _ _ _ _ * W),mul_pow (topH ..) W n,mul_pow (u*v) W n]; ring
     rw[mul_comm]; exact le_of_mul_le_mul_left h (mul_pos hu hv)
lemma glowK {S:Scheme}{R:Side}{ℓ i n:ℕ}(A:Massive.Run S n R 6) (s:Averaging)(Y: Cover→ Insertion (S.side R n) 6)(Q: Cover→ Insertion (S.side R i) 6) (t:ℝ) (he:i≤n) (a:Cover): checkE A ℓ s (fun j=> (t:ℂ) • Y j) (fun j=> (t:ℂ) • Q j) a= (t:ℂ) • checkE A ℓ s Y Q a:=by
      have hx(b:Cover): climbH A i n (((t:ℂ) • Q b) :Density (S.side R i) 6)= (t:ℂ) • climbH A i n (Q b):=by
           suffices h:∀ i,∀ y:Stud (S.side R i) 6,i≤ n→climbH A i n ((t:ℂ) • y)=(t:ℂ) • climbH A i n y by exact h _ _ he
           intro i y hi; induction hi using Nat.decreasingInduction with|self=> rw[same,same]|of_succ i hi ih=> rw[Lyre.next A _ hi,Lyre.retreat,Lyre.next A _ hi]; exact ih _
      unfold checkE checkedT; change (Averaging.filter _ _ _ _)- _=_; rw[smul_sub]; congr 1
      · rw [show (fun j:Cover=> climbH A i n ⇑((t:ℂ) • Q j))=(fun j=> t • climbH A i n (Q j)) from funext hx]; exact voleur (fun j=>climbH A i n (Q j)) t _ _ s
      funext v; exact ContinuousMap.congr_fun (voleur Y t (ratioTo S n ℓ • a) (ratioTo S n ℓ) s) v
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.glowK
#print axioms YM.Intag.CardsT.tributeRoot
