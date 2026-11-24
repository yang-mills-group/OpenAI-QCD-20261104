import YM.QCD.Fold.Kit
import YM.QCD.Bay.High
set_option linter.unusedSectionVars false
/-! # Fold a Pack. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{D B b k:ℕ}{a e r w:ℝ}
structure Collum (f F:Side)(I J:Type) (D:ℕ) where
 small : I→Site f
 big : J→ Site F
 T : Window f F D
 pi : J → I
 orient : J→ℂ
 d : f.val ∣ F.val
 hv : (⇑(splitter d))=T.cut
 nest p : small (pi p)=T.cut (big p)
-- use casts h if necessary
variable {I J:Type} [DecidableEq I] [Fintype I][DecidableEq J][Fintype J]
variable (S:Collum f F I J D)(X:Land F J J)(Y:Pays F J J)
variable {M:Grid F →ArrayL J J}{m:Grid f→ArrayL I I}
namespace Collum
def rim (u v:J):= star (S.orient u)*S.orient v
structure Receives (M:Grid F →ArrayL J J)(m:Grid f→ArrayL I I): Prop where
 foldP : Fold S.pi D
 units i : ‖S.orient i‖=1
 cells U i j : cell (m U) (S.pi i) j=∑ K∈parcel S.pi j,S.rim i K • cell (M (S.T.links U)) i K

lemma today (H:S.Receives M m)(j k):‖S.rim j k‖=1:=by rw [rim,norm_mul,norm_star,H.units,H.units,mul_one]
include S
lemma height:0<D:=by -- no implicit variant T gives card wake
    have he:=S.T.fold (S.T.cut 0); exact he ▸ card_pos.mpr ⟨0,(posted ..).mpr rfl⟩
-- pack
variable (b B:ℕ)
def cloud : Land f I I:= fun i j u=>(D:ℝ)⁻¹ • ∑ p∈parcel S.pi i,∑ q∈parcel S.pi j,∑ w,floret S.T S.d (S.rim p q) b B (S.big p) (S.big q) w (X p q w) u

def payC : Pays f I I := fun i j u=>(D:ℝ)⁻¹ *∑ p∈parcel S.pi i,∑ q∈parcel S.pi j,∑ w,flora S.d b B (S.big p) (S.big q) w (Y p q w) u
lemma folded (hp:Pack S.big S.big a e b M r X Y)(u:S.Receives M m) i j U: Crop (S.small i) (S.small j) a U (S.cloud X b B i j U) (S.payC Y b B i j U):=by
    unfold cloud payC; let A (p q) w:=floret S.T S.d (S.rim p q) b B (S.big p) (S.big q) w (X p q w) U; let T p q w:=flora S.d b B (S.big p) (S.big q) w (Y p q w) U
    have hi p (hi:p∈parcel S.pi i) q (hj:q∈parcel S.pi j) w : Crop (S.small i) (S.small j) a U (A p q w) (T p q w) :=by
        have he:S.pi p=i:= (posted ..).1 hi; have hf:S.pi q=j:= (posted ..).1 hj; rw [← he,← hf,S.nest,S.nest]; exact loan_crop _ _ _ _ _ (S.today u ..) S.hv (hp.crop p q w) U -- edit
    have hh:= Crop.cluster (parcel S.pi i) fun p he=> Crop.cluster (parcel S.pi j) fun q hv=> Crop.cluster univ fun w _=> hi p he q hv w
    let n:ℝ:= D; have hn: 0<n:= Nat.cast_pos.mpr S.height; have hu := hh.alloy (↑(n⁻¹):ℂ); rw [Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr hn).le] at hu; exact hu
lemma flurry (hp:Pack S.big S.big a e b M r X Y)(hv:4*B+3<f.val)(p q Z):
    (∑ V: Support f,∑ w,floret S.T S.d (S.rim p q) b B (S.big p) (S.big q) w (X p q w) V (settled Z))=S.rim p q • cell (M (S.T.links Z)) p q:=by
   rw [Finset.sum_comm]; simp_rw [← Finset.sum_apply,full_fl S.T S.d _ b B _ (S.big p) (S.big q) hv]; simp only [Finset.sum_apply, Pi.smul_apply,comp_apply,← pose, ← smul_sum,hp.sells]
lemma accepts (hp:Pack S.big S.big a e b M r X Y)(hv:4*B+3<f.val)(H:S.Receives M m) (i j:I)(U):
 (∑ V:Support f,S.cloud X b B i j V (settled U))=cell (m U) i j:=by
   simp only [cloud, Pi.smul_apply,Finset.sum_apply,← smul_sum]; rw [Finset.sum_comm]; conv_lhs=>arg 2; arg 2; intro p; rw [Finset.sum_comm]
   simp_rw [S.flurry _ _ _ _ hp hv] -- implicit
   rw [sum_congr rfl (show ∀ p ∈ parcel S.pi i,(∑ q ∈ parcel S.pi j,S.rim p q • cell (M (S.T.links U)) p q)=cell (m U) i j from fun i hi=>((posted ..).1 hi) ▸ (H.cells U i j).symm)]
   rw [sum_const,H.foldP, ← Nat.cast_smul_eq_nsmul ℝ,inv_smul_smul₀ (show (D:ℝ)≠0 from (Nat.cast_pos.mpr S.height).ne')]

lemma coal (hp:Pack S.big S.big a e b M r X Y)(hv:4*B+3<f.val)(he:0≤e)(i j:I):
    duel (S.payC Y b B) i j e b ≤(D:ℝ)⁻¹ * ∑ p∈parcel S.pi i,∑ q∈parcel S.pi j,duel Y p q e b:=by
  unfold duel payC; simp_rw [mul_left_comm (rent e b _) (D:ℝ)⁻¹, ← mul_sum]; apply mul_le_mul_of_nonneg_left _ (by positivity); simp_rw [mul_sum]; rw [Finset.sum_comm]; refine sum_le_sum fun p _=>?_ ; rw [Finset.sum_comm]; refine sum_le_sum fun q _=>?_ ; rw [Finset.sum_comm]; exact sum_le_sum fun w _=>full_f _ b B _ _ hv (hp.crop ..).1 he
lemma gatherC {E:Type*}[AddCommMonoid E](Z:J→E) : (∑ i:I,∑ j∈parcel S.pi i, Z j)=∑ i,Z i:=by classical
   convert! Finset.sum_fiberwise univ S.pi Z using 2; case _ i=>
    congr 1
    ext; simp [posted]
lemma plates (hp:Pack S.big S.big a e b M r X Y)(hv:4*B+3<f.val)(H:S.Receives M m)(he:0≤e):Pack S.small S.small a e b m r (S.cloud X b B) (S.payC Y b B):=by
    let q:ℝ:= D; have hg:0<q:=Nat.cast_pos.mpr S.height
    refine ⟨S.folded _ _ _ _ hp H,S.accepts _ _ _ _ hp hv H,?_,?_⟩
    · intro i; refine (sum_le_sum (fun j _=>S.coal X Y b B hp hv he i j)).trans ?_ ; rw [← mul_sum,Finset.sum_comm]; simp_rw [S.gatherC]
      have hh:= sum_le_sum (s:=parcel S.pi i) (fun p _=>hp.spends p); rw [sum_const,H.foldP,nsmul_eq_mul] at hh
      exact (mul_le_mul_of_nonneg_left hh (inv_pos.mpr hg).le).trans_eq (inv_mul_cancel_left₀ hg.ne' _)
    intro i; refine (sum_le_sum (fun j _=> S.coal X Y b B hp hv he j i)).trans ?_ ; rw [← mul_sum, S.gatherC,Finset.sum_comm]; have hh:= sum_le_sum (s:=parcel S.pi i) (fun p _=> hp.dues p); rw [sum_const,H.foldP,nsmul_eq_mul] at hh; exact (mul_le_mul_of_nonneg_left hh (inv_pos.mpr hg).le).trans_eq (inv_mul_cancel_left₀ hg.ne' _)
end Collum
end YM.QCD.Folding
