import YM.QCD.Rudder.Watch
import YM.RG.PathActions

/-!
# path-curvature bilinear atoms at degree m preserve gauge and winding
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rudder
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology InnerProductSpace
variable {n : Side} {I J : Type} {m j : ℕ}
structure Bloom (m : ℕ) where
  tail : Walk
  petals : Fin m→ RG.Slot
  coeff : (Fin m → su.ColorIndex)→ Bundle
namespace Bloom
variable (W : Bloom m)

def hues (v : Fin m→ su.Color) :=∑ i : Fin m→su.ColorIndex, ((∏ j,v j (i j): ℝ):ℂ) • W.coeff i
def taste (U : Grid n) (x : Site n) := W.hues fun i=> (W.petals i).atSite U x
def Spins := ∀ u (v : Fin m→su.Color), W.hues (fun i=> su.adjoint u (v i)) = touch (colour u)* W.hues v * star (touch (colour u))
def tonic (t : Site n) (U : Grid n):= rides (Equiv.refl _) (W.taste U) * routeM t U W.tail
lemma slotRot (U : Grid n) (x : Site n) (r: RG.Slot) (g : Frame n): r.atSite (gauge g U) x= su.adjoint (g x) (r.atSite U x):=by
  simp only [Slot.atSite, Slot.eval, expandAt_gauge,travel_gauge, face_gauge,Gauge.curvature_conjugate,Gauge.adjoint_mul,map_zero,zero_add];
  simp only [Slot.offset] -- invite
  rw [← Gauge.adjoint_mul su ((g ((wrap n) (stop 0 r.walk)+x))⁻¹) (g ((wrap n) (stop 0 r.walk)+x)), inv_mul_cancel,Gauge.adjoint_one]
lemma toneRotation (U : Grid n) (x : Site n) (t : Site n) (g : Frame n) (h : W.Spins) : W.tonic t (gauge g U) = siteRot g*W.tonic t U *star (siteRot g):=by
  have hp : rides (Equiv.refl _) (W.taste (gauge g U))=siteRot g* rides (Equiv.refl _) (W.taste U) *star (siteRot g) := by
    unfold siteRot; rw [ride_ad,ride_mul,ride_mul]; congr 1; funext i; unfold taste; simp_rw [slotRot]; rw [h]; rfl
  rw [tonic,hp,gaugeM,Pine.composed1]; rfl
lemma slotOne (r : RG.Slot) : r.atSite (G:=su) 1 (0:Site n)=0:=by
  have he (x : Cover) (w : Walk): travel (expandAt (0:Site n) (1:Grid n)) x w=1:=by induction w generalizing x with
  | nil=>rfl
  | cons a w ih=>rw [Lattice.travel,ih,mul_one]; simp [Step.read,expandAt]
  unfold Slot.atSite Slot.eval faceValue; rw [he,he, Gauge.curvature_unit]; simp
lemma slot_tail (r : RG.Slot) (x : Site n) : r.atSite (G:=su) 1 x=0:=by
  rw [show r.atSite (G:=su) 1 x=r.atSite 1 (0:Site n) from rfl]; exact slotOne ..
lemma tonic_one (t : Site n) (h:0<m): W.tonic t 1=0:=by
  have ht (x:Site n): W.taste 1 x=0:=by
    unfold taste hues; refine sum_eq_zero fun i _=>?_; simp_rw [slot_tail]; rw [prod_eq_zero (mem_univ (⟨0,h⟩:Fin m)) rfl, Complex.ofReal_zero,zero_smul]
  unfold tonic; simp_rw [funext ht]; rw [ride_zero,zero_mul]

def price := ∑ i, ‖W.coeff i‖
def span := W.tail.length+∑ i,(W.petals i).length
def paid (δ : ℝ):= Real.exp (δ*W.span)*W.price
lemma price_nn : 0≤ W.price:= by unfold price; positivity
lemma paidUp {δ : ℝ} (hd : 0≤δ) : W.price≤ W.paid δ := le_mul_of_one_le_left W.price_nn (Real.one_le_exp (by positivity))
lemma nook (r : Slot) (U : Grid n) (x:Site n) (i : su.ColorIndex) : |((r.atSite U x) i:ℝ)|≤2 := ((show |((r.atSite U x) i:ℝ)|≤ ‖r.atSite U x‖ from by rw [← EuclideanSpace.basisFun_inner]; exact (abs_real_inner_le_norm ..).trans (le_of_eq (by rw [OrthonormalBasis.norm_eq_one,one_mul])))).trans (Slot.eval_norm ..)
lemma tonicBudget (t : Site n) (U : Grid n): ‖W.tonic t U‖≤2^m* W.price:=by
  unfold tonic; apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (rotation_price (circle ..))).trans; apply Kit.rides_size _ (mul_nonneg (by positivity) W.price_nn); intro x;
  unfold taste hues price; rw [mul_sum]; refine (norm_sum_le ..).trans (sum_le_sum ?_); intro i _; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs, Finset.abs_prod]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); simpa using Finset.prod_le_prod (s:=univ) (fun j _=> abs_nonneg ((W.petals j).atSite U x (i j))) fun j _=>nook _ _ _ (i j) -- check indentation
end Bloom
structure Fractal (G : I→Bloom m) (δ p : ℝ): Prop where
  degree : 0≤δ
  sect (i:I): (G i).Spins
  bills : Summable fun i=> (G i).paid δ
  bill : (∑' i,(G i).paid δ) ≤ p
variable {δ C : ℝ} {G : I→Bloom m} (h : Fractal G δ C)
include h
lemma Fractal.priced : Summable fun i=> (G i).price:= h.bills.of_nonneg_of_le (fun i=> (G i).price_nn) fun i=> (G i).paidUp h.degree
lemma Fractal.tonics (t : Site n) (U : Grid n): Summable fun i=> ‖(G i).tonic t U‖:= (h.priced.mul_left (2^m)).of_nonneg_of_le (fun i=> norm_nonneg _) (fun i=> (G i).tonicBudget ..)
end YM.QCD.Rudder
