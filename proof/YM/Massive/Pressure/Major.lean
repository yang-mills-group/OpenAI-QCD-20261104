import YM.Next.RANK.Determinant
import YM.Massive.Pressure.Triangle
/-!
# Prices with the current scale (use also with exterior-valued activities)

Elements of Next.RANK.Determinant, using inequality to the reference β (not equality).
No assumption of pure YM activities laws. Powers needed for the lower match to pressure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Pressure
open Lattice Wilson RG Function MeasureTheory Filter Set SectorNext.Vacuum Next.Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ENNReal
variable {G : Gauge} {n f : Side} {σ A Λ β g : ℝ} {p0 : BudgetPoint} {t : Clip} {P : PathData G}
lemma base_price {g : ℝ} (hg : 0<g) (hm : 1 ≤ β*g^2) (he : g≤p0.threshold) (U : Config G n) (p : Face (Per n)) :
    G.chord (faceValue U p) / (g / strength t) - 1 ≤ β*P.baseTerm t p0 U p := by
  let c := strength t
  let a := G.chord (faceValue U p)
  have hc : 0 < c := strength_pos t
  have hn : 0 ≤ a := G.chord_nonneg _
  have hp : 0 ≤ β := by by_contra! h; linarith only [hm,mul_nonpos_of_nonpos_of_nonneg h.le (sq_nonneg g)]
  have hq : c ≤ t.linear := min_le_right ..
  have ht : c ≤ t.direct := by have := t.kink; linarith
  have heq : a/(g/c)=c*(a/g) := by field_simp
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (show PathData.clipped t p0.threshold a ≤ _ from ?_) hp)
  · change a/(g/c) - _ ≤ _; rw [heq]; unfold PathData.clipped
    split_ifs with HF
    · calc
        _ ≤ c*((a/g)^2)/2 := by
          have hj : 0 ≤ c*((a/g)-1)^2 := mul_nonneg hc.le (sq_nonneg _)
          have hv : c ≤ 1 := strength_le_one _
          nlinarith only [hj, hv]
        _ = (1/g^2) * (c*a^2/2) := by ring
        _ ≤ β * _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ (pow_pos hg 2)).mpr hm) (by positivity)
        _ ≤ β * (t.direct * a^2 / 2) := by gcongr
    · calc
        _ ≤ c * (a/g) := by linarith only
        _ ≤ β * (t.linear*g*a) := by
          have hs : 0≤a/g := div_nonneg hn hg.le
          apply le_trans (mul_le_mul_of_nonneg_right hq hs); refine le_trans ?_ (mul_le_mul_of_nonneg_right ((div_le_iff₀ (pow_pos hg 2)).mpr hm) (show _ from ?_)); apply le_of_eq; field_simp
          have h := t.tail_pos; positivity
        _ ≤ _ := by gcongr; exact t.tail_pos.le
  classical
  unfold PathData.baseTerm
  split <;> simp [a]; positivity


lemma exponent_retains (h : P.Bounds t σ A Λ) {g : ℝ} (hg : 0<g) (he : g≤p0.threshold) (hm : 1 ≤ β*g^2) (U : Config G n) :
    ∑ p : Face (Per n), G.chord (faceValue U p)/(g/strength t) -
      (Fintype.card (Site n):ℝ)*(PathData.loopsPrice p0 β A Λ + Fintype.card PlaqAxes) ≤ P.inChannels t p0 β U := by
  let Gc := g/strength t
  let F (W : Config G n) := ∑ p : Face (Per n), G.chord (faceValue W p) / Gc
  have s (k : Signed) : F (pull k 0 U)=F U := by
    unfold F; simp_rw [Face.send_price U _ k 0 G.chord G.chord_inv (fun _ u => G.chord_conj u _)]
    let e : Equiv.Perm (Face (Per n)) := Equiv.ofBijective (Face.send k 0) ⟨Face.injective_send k 0,
      Finite.injective_iff_surjective.mp (Face.injective_send k 0)⟩
    exact Equiv.sum_comp e (fun x => G.chord (faceValue U x)/Gc)
  let q : ℝ := Fintype.card (Site n)
  let a : ℝ := Fintype.card PlaqAxes
  let v := PathData.loopsPrice p0 β A Λ
  have heq (W : Config G n) : (∑ p : Face (Per n), (G.chord (faceValue W p)/Gc-1))=F W - q*a := by
    unfold F q a; rw [Finset.sum_sub_distrib]; simp [Face,Site]
  have hf (k : Signed) : F U - q*a-q*v ≤ P.principal t p0 β (pull k 0 U) := by
    let W := pull k 0 U
    have H := Finset.sum_le_sum fun i (_:i∈Finset.univ) => base_price (P:=P) (t:=t) hg hm he W i
    change (∑ p : Face (Per n), (G.chord (faceValue W p)/Gc-1))≤_ at H
    rw [← Finset.mul_sum,heq,s k] at H
    have hj := (abs_le.mp (P.volume_price t p0 _ (show 0 ≤ β from by by_contra! h'; linarith only [hm,mul_nonpos_of_nonpos_of_nonneg h'.le (sq_nonneg g)]) W h)).1
    change -(q*v) ≤ _ at hj
    linarith only [hj,H]
  have huv := (Branch.avg_const (n:=Signed) (F U-q*a-q*v)).symm.le.trans (Branch.avg_mono hf)
  change F U - q*a-q*v ≤ P.inChannels t p0 β U at huv
  change F U-_ ≤ _
  unfold v q a at huv
  linarith only [huv]

def major (G : Gauge) (n : Side) (A g : ℝ) (V : Config G n) :=
  Real.exp ((Fintype.card (Site n):ℝ)*A-∑ p : Face (Per n), G.chord (faceValue V p)/g)

@[fun_prop] lemma major_cont (G : Gauge) (n : Side) (A g : ℝ) : Continuous (major G n A g):=by unfold major faceValue; fun_prop

lemma integral_major (L : HaarBudget G) (A : ℝ) (hg : 0 < g) (hn : 1 < n.val) :
    (∫ U,major G n A g U ∂prior G n) ≤ Real.exp ((Fintype.card (Site n):ℝ)*A) * (L.big*g^G.lieDim)^rich n:=by
  classical
  let v (x:G.El):= Real.exp (-(G.chord x/g))
  have hv : Continuous v:=by unfold v; fun_prop
  let q:ℝ := Fintype.card (Site n)
  have he U : major G n A g U= Real.exp (q*A)*∏ p:Face (Per n), v (faceValue U p):=by unfold major v; rw [← Real.exp_sum, ← Real.exp_add, Finset.sum_neg_distrib,sub_eq_add_neg]
  simp_rw [he]; rw [integral_const_mul]; refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos (q*A)).le
  exact ((Next.Rank.Axial.elimination hn v hv (fun u=>(Real.exp_pos _).le) (fun u=>Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (G.chord_nonneg u) hg.le)))).trans (pow_le_pow_left₀ (integral_nonneg fun i=>(Real.exp_pos _).le) (L.high _ hg) _))
end YM.Massive.Pressure
#print axioms YM.Massive.Pressure.integral_major
