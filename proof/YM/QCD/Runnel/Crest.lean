import YM.QCD.Runnel.Proof

/-! # payoff. Post-L integrable path price for reference high Gaussian -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Run
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
variable {s f L : Side} {M X : St f} {δ b c g q ε R D u w : ℝ} {B v n p j k : ℕ}

def logchip (M : Sheet f) (i:ℕ):= - (((i+1:ℂ))⁻¹ • M^(i+1))
def lap (M : Sheet f):=∑' i, logchip M i
lemma mark_norm (M : Sheet f) (i): ‖logchip M i‖ ≤ ‖M‖^(i+1):=by
  unfold logchip; rw [norm_neg,norm_smul,norm_inv]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_) (Cost.power_bill ..); rw [show ‖(i+1:ℂ)‖= (i+1:ℝ) by norm_cast]; exact inv_le_one_of_one_le₀ (by simp)
lemma log_series {M : Sheet f} (h : ‖M‖<1): Summable (logchip M):=by
  apply ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg M) h)).of_norm_bounded; exact mark_norm M
lemma stamped (H : Sheet f) (h : Chiral (chirality _) H) (hp : 0<H.det.re) (hw : 0<w) (ht : ‖notch w H‖ < 1):
    Real.log H.det.re=(∑ i : Site f, (cell (lap (notch w H)) i i).trace.re)- Fintype.card (Row f)*Real.log w:=by
  let Z:=notch w H
  conv_lhs=> rw [← show ‖H.det‖=H.det.re by conv_lhs=> rw [← Cost.determinant_real chi_sq h,Complex.norm_real,Real.norm_of_nonneg hp.le]]
  rw [Cost.marks H hw ht]; congr 1
  have he (k : Row f) : (lap Z) k k = - ∑' i, Cost.plank Z k i:=by
    let M : Sheet f →ₗ[ℂ] ℂ := { toFun:=fun z=> z k k,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
    have hp : HasSum (fun i=> logchip Z i k k) ((lap Z) k k) := M.toContinuousLinearMap.hasSum (log_series ht).hasSum
    rw [← hp.tsum_eq, ← tsum_neg]; refine tsum_congr fun i=>?_ ; rw [logchip,Cost.plank,Matrix.neg_apply,Matrix.smul_apply]; congr 1; ring
  rw [Fintype.sum_prod_type, ← sum_neg_distrib]; apply sum_congr rfl; intro i _
  unfold Matrix.trace; rw [← sum_neg_distrib,Complex.re_sum]; exact sum_congr rfl fun j _=>by change _=((lap Z) (i,j) (i,j)).re; rw [he,Complex.neg_re, Complex.re_tsum (planked Z ht _)]

def offer (R g : ℝ) := (∑' i:ℕ,R*g^i)
def offerZ (w R g : ℝ) := (∑' i:ℕ,w*(R*g^i))
lemma offer0 (h : 0≤g) (hq : 0≤R):0≤ offer R g:=tsum_nonneg fun i=>by positivity
lemma offerZ0 (h : 0≤g) (hq : 0≤R) (hw : 0<w):0≤ offerZ w R g:=tsum_nonneg fun i=>by positivity
lemma LapPack (h : ∀ i:ℕ,Own f δ b B (M^i) (R*g^i)) (hd : 0<δ) (hb : 0≤b) (hp : 0<g) (hg : g<1) (he : ∀ U, ‖M U‖<1) (hR : 0<R) : Own f δ b B (fun U=>lap (M U)) (offer R g):=by
  have ht:= (summable_geometric_of_lt_one hp.le hg).mul_left R
  refine Heritage.congregation (T:=fun i U=>logchip (M U) i) hd hb (fun i=> ?_) ht (fun U=> (log_series (he U)).hasSum)
  have hh:= ((h (i+1)).scalar ((i+1:ℂ)⁻¹)).minus
  have hu : ‖(i+1:ℂ)⁻¹‖≤1:=by rw [norm_inv, show ‖(i+1:ℂ)‖= (i+1:ℝ) by norm_cast]; exact inv_le_one_of_one_le₀ (by simp)
  apply (show Own f δ b B (fun U=>logchip (M U) i) (‖(i+1:ℂ)⁻¹‖*(R*g^(i+1))) from ?_).mono ((mul_le_of_le_one_left (by positivity) hu).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hp.le hg.le (by omega)) hR.le))
  simpa only [logchip, funext_iff, Own] using! hh -- check

variable (P : Plan j)
structure Arbor (L : Side) (k : ℕ) (b w q g R δ Y : ℝ) (m : ℕ) : Prop where
 pos : 0<w
 safe : 0≤q
 ceil : q<1
 solid : 0<R
 pays : 0<g
 grade : g<1
 tube : 0<δ
 soaring : 0<Y
 uses (F : Flight j k) (_ : F.L=L) (s f : Side) (h:f.val=s.val*F.L.val) (B : ℕ) (hv : m≤B) (t):
    let H:=vaultF P F h t; let X:=fun U=> notch w (H U)
    Wing (sliceL F h) (tied F h t) δ b B Y ∧ (∀ U, ‖X U‖≤q) ∧ ∀ i:ℕ, Own f δ b B (X^i) (R*g^i)
lemma groves (L : Side) (k : ℕ) (hb : 0≤b):∃ w q g R δ Y m, Arbor P L k b w q g R δ Y m:=by
  obtain ⟨d₁,d,c,C,w,q,g,R,V,m,r,v,h₁,h₂,H,hU,hm,hp,hq,hg0,hg1,hR,hV,hM⟩ := obtain_powers (k:=k) P b hb L
  refine ⟨w,q,g,R,d₁,tubeY L b c j r,m,h₁,hp,hq,hR,hg0,hg1,h₂,tubeY_pos ..,?_⟩; intro F hQ s f h B hv t X K; have he:=hM F hQ s f h B hv t
  refine ⟨?_,he.1,he.2.2.2⟩; subst L; have hq:= rectify F h t H.hb H.hd H.hc H.hr (hm.trans hv) H.hg; exact ⟨hq.1.clip hU,hq.2.clip hU⟩
namespace Arbor
variable {P} {m} {Y} (hu : Arbor P L k b w q g R δ Y m) (F : Flight j k) (hh : F.L=L) (h:f.val=s.val*F.L.val) (hb : 0≤b) (hp : m≤B) (t : Site f)
include hu hh hb hp
lemma prettyLap : Own f δ b B (fun U=> lap (notch w (vaultF P F h t U))) (offer R g):=by
  have hi:= hu.uses F hh s f h B hp t; exact LapPack hi.2.2 hu.tube hb hu.pays hu.grade (fun U=> (hi.2.1 U).trans_lt hu.ceil) hu.solid
lemma returnable : Own f δ b B (fun U=> (vaultF P F h t U)⁻¹) (offerZ w R g):=by
  have he:= hu.uses F hh s f h B hp t
  let X:St f:= fun U=> notch w (vaultF P F h t U)
  have hh n: Own f δ b B ((w:ℂ) • X^n) (w*(R*g^n)):=by
    have e:= (he.2.2 n).scalar (w:ℂ); rw [Complex.norm_real, Real.norm_of_nonneg hu.pos.le] at e; exact e
  have hm := ((summable_geometric_of_lt_one hu.pays.le hu.grade).mul_left R).mul_left w
  refine Heritage.congregation hu.tube hb hh hm (fun U=> ?_); simp_rw [Pi.smul_apply,Pi.pow_apply]; exact Cost.chip _ hu.pos.ne' (ticket_inv ..) ((he.2.1 U).trans_lt hu.ceil)
lemma carriage :
    Heritage (sliceL F h).embed (sliceL F h).embed δ b B (fun U=> 1- (tied F h t U)*((vaultF P F h t U)⁻¹)*(tied F h t U)ᴴ) (Real.exp b+Y*offerZ w R g *Y):= by
  have he := (hu.uses F hh s f h B hp t).1; have hK:= offerZ0 hu.pays.le hu.solid.le hu.pos
  change Heritage _ _ _ _ _ _ ((Real.exp b+Y*offerZ w R g*Y)) -- arithmetic check
  exact (Heritage.heritage_one _ hb).sub ((he.1.meet (hu.returnable F hh h hb hp t) hu.tube hb hu.soaring.le hK).meet he.2 hu.tube hb (mul_nonneg hu.soaring.le hK) hu.soaring.le)
end Arbor
end YM.QCD.Run
