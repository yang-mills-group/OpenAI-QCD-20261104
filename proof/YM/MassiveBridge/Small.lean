import YM.MassiveBridge.Inserts
import YM.Fields.Tall
/-!
# The center operator for all fields on the one cap, its quantitative bound

Matrix/shot conventions of `Boundary.Small` now with F.W itself.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Function Set Filter MeasureTheory Mink Spectral Complex
open OS (Cross)
open OS.Semigroup (duration)
open Boundary (Times Heights SpacePoints shift trace place)
-- width geometry independent of hierarchy
open Boundary.Small (interval enough lit down bufferF logD ample)
open scoped Topology NNReal BigOperators InnerProductSpace ComplexOrder
variable {X : Fields} {S : X.Kernel} {n : ℕ} {C : Chamber S timeAxis}

structure MatrixCap (C : Chamber S timeAxis) where
  bar (u : ℝ≥0) : X.W →ₗ[ℂ] C.H.Op
namespace MatrixCap
variable (B : MatrixCap C)
def center (p : ℝ≥0) (v : X.W) : Plant X := (position 0 p,v)
def concretized (P : Spread C) := ∀ v (p : ℝ≥0), 0<p →
    B.bar p v = P.place (p+p) [center p v]
def rip (w : ℂ) (t) (x : Space3) := (C.flow.F (interval w t)).comp (C.flow.U (bufferF x))

lemma flanks (w : ℂ) (t : ℝ≥0) (x : Space3) (v : C.H)
    (h : (t:ℝ)<w.im) : ‖rip (C:=C) w t x v‖ ≤ ‖v‖ := by
  have he := (C.flow.F (interval w t)).le_opNorm (C.flow.U (bufferF x) v)
  rw [C.flow.unitary] at he
  exact he.trans (mul_le_of_le_one_left (norm_nonneg _) (C.flow.norm_row ((down _ _).2 h)))

/-- product recursively of all bars after first. -/
def trainB (p : ℝ≥0) : ∀ n, Times n → SpacePoints n → (Fin n → X.W) → ℂ → Space3 → C.H
  | 0,_,_,_,_,_ => C.omega
  | n+1,z,x,v,Z,X =>
      rip (z 0-Z) (p+p) (x 0-X) ((B.bar p (v 0)) (trainB p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)))

def matrix (p : ℝ≥0) : ∀ n, Times n → SpacePoints n → (Fin n → X.W) → ℂ
  | 0,_,_,_ => inner ℂ C.omega C.omega
  | n+1,z,x,v => inner ℂ C.omega (B.bar p (v 0) (B.trainB p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)))

def shot (p : ℝ≥0) : ∀ n, (Fin n → X.W) → Heights n → Points n → C.H
  | 0,_,_,_ => C.omega
  | n+1,v,y,k => let z := shift k y; let x := trace k
                 rip (z 0) p (x 0) (B.bar p (v 0) (B.trainB p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)))

def rated (v : X.W) := ∃ C : ℝ, ∃ A : ℕ, 0 < C ∧ ∀ p : ℝ≥0, p ∈ Ioo 0 1 →
    ‖B.bar p v‖ ≤ C*(p:ℝ)⁻¹^A


theorem centerTime (p : ℝ≥0) (v : X.W) : (center p v).1 timeAxis = (p:ℝ) := time_position _ _
lemma centeredSlab (p : ℝ≥0) (v : X.W) (h : 0 < p) : Slab timeAxis (p+p) [center p v] := by
  have hv : 0 < (p:ℝ) := h
  refine ⟨add_pos h h,⟨locations.mpr (by simp),?_⟩,?_⟩ <;>
    simpa only [List.mem_singleton,forall_eq,centerTime,NNReal.coe_add,lt_add_iff_pos_right] using hv
lemma centeredBuffer (p : ℝ≥0) (v : X.W) : buffer timeAxis p (p+p) [center p v] := by
  refine ⟨?_,?_⟩
  · intro i j h
    exact (h (Subsingleton.elim (α := Fin 1) i j)).elim
  simp [centerTime]

lemma matrix_elem (A : Spread C) (v : X.W) (p : ℝ≥0) (hp : 0<p) (x y : Future X timeAxis) :
    inner ℂ (C.GNS.plant x) (A.place (p+p) [center p v] (C.GNS.plant y)) =
    oneIn (reflect x.val timeAxis) (raised timeAxis (p+p) y.val) (position 0 p) S v := by
  rw [A.reads (centeredSlab p v hp) y,C.GNS.measure]; rfl

lemma op_ext {M N : C.H.Op}
    (h : ∀ x y, inner ℂ (C.GNS.plant x) (M (C.GNS.plant y)) = inner ℂ (C.GNS.plant x) (N (C.GNS.plant y))) :
    M = N := by
  apply C.GNS.by_bud; intro y; apply C.GNS.whole.eq_of_inner_right ℂ; intro x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,inner_add_left,hf,hg]
  | single i c => simp only [YM.Kernel.Gram.stems,Finsupp.linearCombination_single,inner_smul_left,h]

def shared (A : Spread C) (p : ℝ≥0) (hp : 0<p) : X.W →ₗ[ℂ] C.H.Op where
  toFun v := A.place (p+p) [center p v]
  map_add' v w := by
    apply op_ext; intro x y
    rw [add_apply,inner_add_right]; simp only [matrix_elem A _ p hp x y,map_add]
  map_smul' c v := by
    apply op_ext; intro x y
    rw [smul_apply,inner_smul_right]; simp only [RingHom.id_apply,matrix_elem A _ p hp x y,map_smul,smul_eq_mul]

lemma affordable (E : Fields.Euclidean S) (full : ∀ x:X.W, ∃ D,x∈ X.level D) (A : Spread C) :
    ∃ B : MatrixCap C, B.concretized A ∧ ∀ v, B.rated v := by
  classical
  let B : MatrixCap C := ⟨fun p => if h : 0<p then shared A p h else 0⟩
  have hc : B.concretized A := by intro v p h; simp [B,h,shared]
  refine ⟨B,hc,fun v => ?_⟩
  obtain ⟨D,hD⟩:= full v
  obtain ⟨m,R,hR,H⟩:= Spread.rated A E 1 D
  let t:ℝ:=‖v‖+1; have ht:0<t:=by unfold t; positivity
  let w : X.W := (↑t:ℂ)⁻¹ • v; have hW : w ∈ X.level D ∧ ‖w‖≤1 := by
    refine ⟨(X.level D).smul_mem _ hD,?_⟩; rw [show ‖w‖=(t⁻¹)*‖v‖ from by simp [w,norm_smul,ht.le]]
    exact (inv_mul_le_iff₀ ht).mpr (by unfold t; linarith)
  refine ⟨(R+1)*t,m, mul_pos (by linarith) ht,fun p h => ?_⟩
  calc ‖B.bar p v‖ = ‖(↑t:ℂ) • B.bar p w‖ := by rw [← map_smul, show (↑t:ℂ) • w = v from smul_inv_smul₀ (by exact_mod_cast ht.ne') _]
       _ = t * ‖A.place (p+p) [center p w]‖ := by rw [hc w p h.1,norm_smul,Complex.norm_real,Real.norm_of_nonneg ht.le]
       _ ≤ t * (R*(p:ℝ)⁻¹^m) := mul_le_mul_of_nonneg_left (H _ _ (centeredSlab p w h.1) rfl (fun x hx=> by obtain rfl:= List.mem_singleton.mp hx; exact hW) _ h.1 (show (p:ℝ)≤1 from h.2.le) (centeredBuffer p w)) ht.le
       _ ≤ _ := by rw [mul_comm (R+1) t, mul_assoc t]; gcongr; linarith
end MatrixCap
end YM.Massive.Bridge
