import YM.Next.FREE_KERNELS.Dispatch
import YM.Next.FREE_KERNELS.Hall
import YM.QCD.Estimate.Charts
import YM.QCD.Pearl.Elegant

/-! # Prices for test tile: symbols of the ACTUAL f covariance of pure Wick propagation
Counting forms with longitudinal penalty undone at curvature. Statements sampling REAL modes (non AP for gluon).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bank
open Lattice Wilson Function Precision Matrix RG Work.F06 Finset Metric
open Laurent Bloch Exterior YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ComplexConjugate InnerProductSpace
variable {c:Side} {k j:ℕ}
open QCD.Pearl (vector_max cap_base)

-- connection inverse with normalized gradient continuation (unused gradient/copotential)
def live (H:Row (TypeFace 2) (TypeFace 2)) (p:Momentum) := mirage 1 1 p * H.read p * signal 1 1 p
def gaugeR (H:Row (TypeFace 2) (TypeFace 2)) (p:Momentum) := live H p + signal 1 0 p*mirage 1 0 p
def spaceK (H:Row (TypeFace 2) (TypeFace 2)) (p:Momentum) := (gaugeR H p)⁻¹
lemma bladeΔ (r:ℕ) (q:Axis→ℂ) : (wedge (r+1) q)ᴴ*wedge (r+1) q+wedge r q*(wedge r q)ᴴ=
    ((sqLength q:ℝ):ℂ) • 1:=by
    rw [wedge_adj, wedge_adj, YM.Next.Free.crossed,_root_.sub_add_cancel]; congr 1
    rw [sqLength_apply,Complex.ofReal_sum]; apply sum_congr rfl; intro i _; rw [Pi.star_apply,Complex.star_def,mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq]
lemma energy (p:Momentum) : q p=tripQ 1 p := by unfold Exterior.q tripQ; simp [chip]
lemma energy_lower {p:Momentum}(hp:p∈baseCube): meter.low^2*‖p‖^2 ≤ sqLength (q p):=by
    have he:= (divisor_real_bounds 1 (base_subset_realCube zone_pos hp)).1
    refine (mul_le_mul_of_nonneg_left (QCD.Pearl.vector_max p) (sq_nonneg _)).trans (he.trans_eq ?_); rw [divisor_normSq 1 hp.1,sqLength_apply,Complex.ofReal_re]; apply sum_congr rfl; intro i _; simp [Exterior.q,seedQ,narrow,chip]
lemma live_gram {H : Row (TypeFace 2) (TypeFace 2)}{p:Momentum}(hp:p∈baseCube) : live H p=(signal 1 1 p)ᴴ*H.read p*signal 1 1 p:=by rw [live,mirage_herm _ p hp.1 1]
lemma gauge_gram {H : Row (TypeFace 2) (TypeFace 2)}{p:Momentum}(hp:p∈baseCube) : gaugeR H p=live H p + signal 1 0 p*(signal 1 0 p)ᴴ:=by rw [gaugeR,mirage_herm _ p hp.1 0]

namespace Charge
open QCD.Cost hiding Floor
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
def Claims (K: Matrix m m ℂ)(b:ℝ) := ∀ p, b*sqLength p≤ pairingRe K p p
omit [DecidableEq n] [DecidableEq m] in
lemma twin_cast (K:Matrix m n ℝ) (x:m→ℂ)(y:n→ℂ) : pairingRe (approached K) x y =
     dotProduct (Complex.re ∘ x) (K *ᵥ (Complex.re ∘ y))+dotProduct (Complex.im ∘ x) (K *ᵥ (Complex.im ∘ y)):=by
     unfold pairingRe; simp only [Matrix.mulVec,dotProduct, Complex.re_sum, Pi.star_apply,
                  Finset.mul_sum, ← sum_add_distrib,Function.comp_apply]; apply sum_congr rfl; intro i _
     apply sum_congr rfl; intro j _; simp [approached,Complex.mul_re,Complex.mul_im]
lemma coil_floor (K:Matrix m m ℝ) (a b:ℝ)(h:Numeric K a b) : Claims (approached K) a := by
    intro x
    have he : sqLength x=pairingRe (approached (1:Matrix m m ℝ)) x x:=by
      unfold pairingRe sqLength; rw [show approached (1:Matrix m m ℝ)=1 by ext i j; by_cases hp:i=j<;>simp [*,approached,Matrix.one_apply],Matrix.one_mulVec]
    rw [he,twin_cast,twin_cast,mul_add,Matrix.one_mulVec,Matrix.one_mulVec]; exact add_le_add (h _).1 (h _).1
lemma mat (K:Matrix m m ℂ)(a:ℝ)(h:Claims K a): QCD.Cost.Floor a K:=by
    intro x
    have he : ‖x‖^2 = sqLength x.ofLp:=by simp [EuclideanSpace.norm_sq_eq,sqLength_apply]
    rw [he]; refine (h x.ofLp).trans_eq ?_
    rw [QCD.Cost.form, PiLp.inner_apply]; unfold pairingRe dotProduct; congr 1; apply sum_congr rfl; intro i _
    rw [RCLike.inner_apply]; exact mul_comm _ _
lemma earns {b:ℝ}{Y : Site c → Matrix m m ℂ}(h:Claims (fiber Y) b)(p:Site c): Claims (Y p) b:=by
    intro u
    let x : Site c × m→ℂ:= fun i=> if p=i.1 then u i.2 else 0
    have he : sqLength u=sqLength x:=by unfold sqLength dotProduct x; simp_rw [Fintype.sum_prod_type]; simp [Pi.star_apply,mul_ite,ite_mul,eq_comm]
    have hx i : (fiber Y*ᵥ x) (p,i)=(Y p *ᵥ u) i :=by simp [Matrix.mulVec,dotProduct,x,fiber,Fintype.sum_prod_type,mul_ite,ite_mul,eq_comm]
    have hh : pairingRe (fiber Y) x x=pairingRe (Y p) u u:=by
       unfold pairingRe dotProduct; rw [Fintype.sum_prod_type,sum_eq_single p]; congr 1; simp_rw [hx]; simp only [Pi.star_apply,x,if_true]
       intro j _ hj; simp [x,hj,Ne.symm hj]; simp
    rw [he,←hh]; exact h x
lemma band {T:Row m m}{a b:ℝ}(hT:T.safe)(h:Numeric (T.acts c) a b) (p:Site c) : Claims (T.read (mon p)) a:=by
    let Z i := T.read (mon (n:=c) i); let M:= approached (T.acts c); let Y:= fiber Z; let F:=rotations c m; let r := (c.val:ℝ)^4
    have hs : 0< r:=pow_pos (side_pos _) _
    have hx : Crew F (r:ℂ):=by dsimp only[r];push_cast; exact rotations_crew c m
    have he : M*F= F*Y:=circulant c T hT
    refine earns (Y:=Z) ?_ p -- mk?
    intro u
    have hh : a*sqLength (F *ᵥ u) ≤pairingRe M (F *ᵥ u) (F *ᵥ u):= coil_floor _ _ _ h _
    have ht : sqLength (F*ᵥu)=r*sqLength u:=by unfold sqLength; rw [volume_dot u u hx]; simp
    have hw : pairingRe M (F *ᵥ u) (F *ᵥ u)= r*pairingRe Y u u := by unfold pairingRe; rw [Matrix.mulVec_mulVec,he,← Matrix.mulVec_mulVec,volume_dot u (Y*ᵥu) hx]; simp
    rw [ht,hw,mul_left_comm] at hh; exact le_of_mul_le_mul_left hh hs

end Charge

def lum (a:ℝ):=min 1 a * meter.low^2
lemma luminous {a:ℝ}(h:0<a): 0<lum a:=mul_pos (lt_min one_pos h) (pow_pos meter.low_pos _)

lemma funds_b (H:Row (TypeFace 2) (TypeFace 2)) {a b:ℝ} (h:Numeric (H.acts c) a b)(he:0<a)(p:Site c)(hH:H.safe):
      QCD.Cost.Floor (lum a *‖mon p‖^2) (gaugeR H (mon p)):=by
    have hu:=mon_mem _ p
    refine Charge.mat _ _ fun u=>?_
    let D := signal 1 1 (mon p); let A := (signal 1 0 (mon p))ᴴ
    have hg : live H (mon p)=Dᴴ * H.read (mon p)*D:=live_gram hu
    have hx: gaugeR H (mon p) = live H (mon p)+ Aᴴ*A:=by rw [gauge_gram hu,show Aᴴ=signal 1 0 (mon p) from Matrix.conjTranspose_conjTranspose _]
    have hv : Dᴴ*D+Aᴴ*A=(↑(sqLength (q (mon p))):ℂ) • 1 :=by unfold D A; rw [Matrix.conjTranspose_conjTranspose,signal_unit,signal_unit]; exact bladeΔ 0 _
    rw [hx,pairingRe_add,hg]; let W:= H.read (mon p); let s:= sqLength u; have hw: 0≤ s:= sqLength_nonneg u
    have h0 : sqLength (q (mon p))*sqLength u = sqLength (D *ᵥu)+sqLength (A*ᵥu) :=by
       rw [← pairingRe_gram,← pairingRe_gram,← pairingRe_add,hv,pairingRe_scale]; unfold pairingRe sqLength; simp
    have hk : pairingRe (Dᴴ*W*D) u u= pairingRe W (D *ᵥu) (D*ᵥ u):=by unfold pairingRe; rw [Matrix.mul_assoc,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, dotProduct_mulVec,← Matrix.star_mulVec] -- direction?
    change _ ≤ pairingRe (Dᴴ*W*D) u u + _
    rw [hk,pairingRe_gram]
    let r:=min 1 a
    have hm : 0≤ r:= le_min zero_le_one he.le
    calc
      _ ≤ r*(sqLength (q (mon p))*sqLength u) := by unfold lum; rw [mul_assoc,mul_assoc,← mul_assoc _ (‖mon p‖^2)]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (energy_lower hu) hw) hm
      _ = _ := ?_
      _ ≤ _ := add_le_add ((mul_le_mul_of_nonneg_right (min_le_right 1 a) (sqLength_nonneg (D *ᵥu))).trans (Charge.band hH h p (D *ᵥu))) (mul_le_of_le_one_left (sqLength_nonneg (A*ᵥu)) (min_le_left 1 a))
    rw [h0,mul_add]
lemma purse (H:Row (TypeFace 2) (TypeFace 2)){a b:ℝ}(h:Numeric (H.acts c) a b)(he:0<a)(p:Site c)(hH:H.safe)(hp:mon p≠0):
    IsUnit (gaugeR H (mon p)).det ∧ ‖spaceK H (mon p)‖ ≤ (lum a *‖mon p‖^2)⁻¹ :=
     let hx:= mul_pos (luminous he) (pow_pos (norm_pos_iff.mpr hp) 2); ⟨(funds_b H h he p hH).unit hx,(funds_b H h he p hH).reciprocal hx⟩
end YM.Bank
#print axioms YM.Bank.purse
