import YM.Lyre.Sweater
import YM.Alum.Arbor
import YM.Alum.Fur
/-!
# Point-cap translated seam cost from both registered cells. Lipschitz slope
of trace moments along AP preserving parity with paid length. Reconciles Theta
with actual prepared sensor by keeping root seam common across halves.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open QCD.Cove Finset NormedSpace QCD.RP
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
namespace Goblet
variable {n c l d:Side}
open Chess Cells Romance Massive.Lyre.Array Plum Patria
variable (T:Tiling n)(R:Regulator n 6)(x y:Stud n 6) (p u v:T.Cell)(a: Axis)
local notation "P₀"=> T.bandCut p a
variable (hR:Goblet.Smoke T R)(hZ:0 < R.Z)
local notation "Δ"=> (step a : Cover)
local notation "g"=> T.mate p a
local notation "θ"=> tallH (T.bandCut p a)
include hR
lemma topsw (hx:Potion x): topH T R x u= topH T R (θ x) (g u):=by
     let l:TapeWalk n T:= [(p,a)]; exact Goblet.earn_eq T hR.seam R u x hx l _ rfl _ (potW (pathT T l) x hx) (SignedEq.refl _)
lemma top_self (hp:Potion x)(hv:u∈T.plusCells p a)(hx: Fence (T.chamber u) x) : ‖meritX R (T.bandCut p a) x x‖ ≤ (topH T R x u)^2:=by
    let z:= T.bandCut p a; let v:Fin 2→ T.Cell:=![g u,u]; let f:Fin 2→ Stud n 6:=![tallH z x,x]
    have hz:Fence (T.chamber ((g) u)) ((θ) x):=hx.tall (Romance.chamber T p u a)
    have hZ: Potion ((θ) x):= potW [P₀] x hp
    have he : ((g) u) ≠ u := fun h=> (T.negative p a u |>.1 ((T.cycles p a u).1 (h.symm ▸ hv))) hv
    have h : ∀ i, Fence (T.chamber (v i)) (f i) ∧ Lyre.Potion (f i):= by intro i; fin_cases i; exact ⟨hz,hZ⟩; exact ⟨hx,hp⟩
    have ht:= wardsP T R hR.seam f v (by
          intro i j hk; fin_cases i <;> fin_cases j <;> first | rfl | exact False.elim (he hk) | exact False.elim (he hk.symm)) [0,1] (by decide) (fun i=>by fin_cases i <;> decide) h hR.real hR.pos hR.cycle hR.energy
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero,Fintype.prod_empty,mul_one,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil] at ht; change ‖meritX R z x x‖ ≤ _; apply le_trans ht
    change topH T R (θ x) (g u) * topH T R x u ≤ _; rw [← topsw T R x p u a hR hp,pow_two]
omit hR
lemma aheadSign (x:Cover)(a:Axis): (Signed.mirror a).act (step a: Cover)=-(step a):=by ext i; by_cases h:i=a <;> simp [Signed.act,Signed.mirror,h,Ne.symm] -- ne
noncomputable abbrev depthShift (b:ℕ)(i:ℕ):Cover:= - (b • (step a:Cover)) + i • step a
include hR
variable (b d:ℕ)(z:ℝ)
local notation "Sᵩ"=> -(b • (step a:Cover))
lemma finerX (hx:u∈ T.plusCells p a)(hz:0 ≤ z)(h:∀ i:ℕ,i ≤4*b→ let y:= Patria.march (depthShift a b i) x; Fence (T.chamber u) y∧ Potion y∧topH T R y u ≤ z): Cozy R (T.bandCut p a) Δ (march (-(b • (step a:Cover))) x) (4*b) (z^2):=by
     let f(i):= depthM Δ (march Sᵩ x) i; have Hp(i):f i=march (depthShift a b i) x:= (marched _ _ x)
     have hF(i:ℕ)(hi:i ≤4*b):Fence (P₀).sector (f i) ∧ ‖meritX R (P₀) (f i) (f i)‖ ≤ z^2 :=by
          rw [Hp]; obtain ⟨h₁,h₂,h₃⟩:=h i hi; exact ⟨h₁.high (T.within p a _ ((T.positive_side ..).mp hx)), (top_self T R _ p u a hR h₂ hx h₁).trans (pow_le_pow_left₀ (top_nn ..) h₃ _)⟩
     exact ⟨fun i h=>(hF i h).1,(hF 0 (Nat.zero_le _)).2,(hF _ le_rfl).2⟩
lemma finerY (hx:u∈T.minusCells p a)(hz:0 ≤ z)(h:∀ i:ℕ,i ≤4*b→ let y:= Patria.march (-(depthShift a b i)) x; Fence (T.chamber u) y∧ Potion y∧topH T R y u ≤ z): Cozy R (T.bandCut p a) Δ (march (-(b • (step a:Cover))) (tallH (P₀) x)) (4*b) (z^2):=by
      let X:= θ x; apply finerX T R X p (g u) a hR b z ((T.cycles ..).2 hx) hz (?_); intro i hi y; let b':= depthShift a b i; obtain ⟨h₁,h₂,h₃⟩:=h i hi; let y':= Patria.march (-b') x; rw [show y=tallH (P₀) y' from ?_]; exact ⟨h₁.tall (Romance.chamber T p u a), potW [P₀] y' h₂,(topsw T R y' p u a hR h₂).symm.le.trans h₃⟩
      have hv: (P₀).flip.act (-b')=b' :=by
           change (Signed.mirror a).actEquiv (-b')=_; dsimp only [b',depthShift]; rw[map_neg,map_add,map_neg,map_nsmul,map_nsmul,show (Signed.mirror a).actEquiv Δ= -Δ from aheadSign 0 a]; rw[smul_neg,smul_neg]; abel
      exact funext fun V=>by
           unfold y' ; rw [commend _ _ P₀ hR.seam,hv] -- `funext V` direction rewrite maybe LHS
include hZ
lemma anchored (hz:0 ≤ z)(hb:0 < b)(hd:d ≤ b)(hx:u∈ T.minusCells p a)(hy:v∈ T.plusCells p a)
      (hX:∀ i:ℕ,i ≤4*b→ Fence (T.chamber u) (Patria.march (-depthShift a b i) x) ∧ Potion (Patria.march (-depthShift a b i) x) ∧topH T R (Patria.march (-depthShift a b i) x) u≤z)
      (hY:∀ i:ℕ,i ≤4*b→ Fence (T.chamber v) (Patria.march (depthShift a b i) y) ∧ Potion (Patria.march (depthShift a b i) y) ∧topH T R (Patria.march (depthShift a b i) y) v≤z) :
    ‖valueH R (x*march ((2*d) • (step a:Cover)) y)-valueH R (x*y)‖ ≤ d*(4*z^2/(b:ℝ)) :=by
       refine Lyre.seams R (T.bandCut p a) Δ x y hR.real hR.seam ?_ hR.pos hZ (aheadSign 0 a) b hb hd (finerY T R x p u a hR b z hx hz hX) (finerX T R y p v a hR b z hy hz hY)
       have ht :=(T.bandCut p a).even; have hh:= hR.cycle; omega
end Goblet
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.Goblet.anchored
