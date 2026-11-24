import YM.Pollen.Chonk
import YM.Pollen.Merges
import YM.Pollen.Road
import YM.Tinus.Kid
import YM.Elix.Erupt
/-!
  SU true polarized vector columns. Controlled detector transportation. C charge orientation.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.PCAC
open Function Filter MeasureTheory QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure
open Entr Entr.Meridian Stew
open QCD.Tide
namespace Oren
variable (a:Flavor 6) (p u:Site c)(s:Signed)(l:Site c→ℂ)(g:Axis)(M:Spike)
open Revolve
local notation "V"=> hues p s l M
local notation "W"=> copies 6 V
local notation "e"=> shiftE s p
local notation "ι"=> s.perm g
local notation "w"=> ((signT s g:ℝ):ℂ)
lemma focus_zone: zone 6 u*W= W*zone 6 (e u):=by
    ext i j; rw [zleft,zright]; by_cases h:e i.1.1=j.1.1
    · simp only [show (j.1.1=e u)=(i.1.1=u) from propext (by rw[← h]; exact (shiftE s p).injective.eq_iff)]
    have hk: W i j=0:=by
         unfold copies; rw [Matrix.blockDiagonal_apply]; split; · rw[hues,rides]; exact if_neg h
         rfl
    rw [hk,ite_self,ite_self]
-- telescope signed at ANY spin M (including adj M=Γ)
variable (h:Glare s (0:Site c) 0 p l)(U:Grid c)
local notation "U'"=> pull s p U
include h
lemma swivel : delta U' g* V= w • (V*delta U (s.perm g)):=by
    have h1:= turned_leg h M U (posDir g); have h2:=turned_leg h M U (negDir g); unfold Stew.delta
    unfold posDir Step.rotate Kit.leg at h1; unfold negDir Step.rotate Kit.leg at h2; cases ht:s.flip g
    · simp only [ht, Bool.xor_self,Bool.false_eq_true,if_false,Bool.true_xor,Bool.not_false,if_true] at h1 h2; rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,h1,h2,← mul_sub,signT,if_neg (by rw[ht]; decide),Complex.ofReal_one,one_smul]
    simp only [ht,Bool.false_xor,Bool.true_xor,Bool.not_true,Bool.false_eq_true,if_false,if_true] at h1 h2; rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,h1,h2,← mul_sub,signT,if_pos ht,Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul,←smul_neg,←mul_neg,neg_sub]
lemma spinK : keel u g a U'*W=W*(w • keel (e u) (s.perm g) a U) ∧ keelB u g a U'*W=W*(w • keelB (e u) (s.perm g) a U):=by
     have he: (delta U' g ⊗ₖ spot a a)*W=w • (W*(delta U (s.perm g) ⊗ₖ spot a a)):=by
          rw [show W=V ⊗ₖ 1 from QCD.Sway.choir_in ..]; rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,mul_one, one_mul, swivel p s l g M h U, Matrix.smul_kronecker]
     constructor
     · unfold keel; rw [mul_assoc,he,Matrix.mul_smul,Matrix.mul_smul,←mul_assoc (zone 6 u),focus_zone, Matrix.mul_assoc] -- check assoc last reuses
     unfold keelB; rw [mul_assoc,focus_zone,←mul_assoc,he,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]
omit h
lemma scales {A:Type*}[Fintype A](b:Bool)(v:ℂ)(P:Sour A)(x:Dirac A): applyMark b (v • P) x=v • applyMark b P x:=by cases b <;> simp only [column,row,Matrix.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum] -- costly
variable (k:Bool)
lemma keyζ {A:Type*}[Fintype A][DecidableEq A](v:ℂ)(P P' QM:Sour A)(hp:QM∈unitary _)(h:P*QM=QM*(v • P'))(x:Dirac A): (Kit.disguise QM) (applyMark k P x)= v • applyMark k P' (Kit.disguise QM x):=by
     let Q:=v • P'; have hW : Q*star QM=star QM*P:=by
          calc
            _=star QM*QM*Q*star QM:=by rw[hp.1,one_mul]
            _=star QM*P:=by rw [mul_assoc _ QM Q,← show P*QM=QM*Q from h,mul_assoc,mul_assoc ..,hp.2,mul_one]
     unfold Kit.disguise; rw [← L_slope k QM (star QM).transpose Q P h.symm (by rw [Matrix.transpose_transpose]; exact hW),show Q=v • P' from rfl]; exact scales ..
include h
variable (hp:Swing s M)
include hp in
lemma meek (X:Lat.Fields c 6): Kit.disguise W (beacon a u g U' X)= w • beacon a (e u) (s.perm g) U (Kit.disguise W X):=by
     change (Kit.disguise W) (applyMark _ _ X-applyMark _ _ X)= w • (applyMark _ _ (Kit.disguise W X)-applyMark _ _ _); rw [map_sub,smul_sub]; have hh := Lat.copies_unitary 6 V (colour_wheel h hp); refine congr_arg₂ (·-·) (keyζ _ w _ _ _ hh (spinK a p u s l g M h U).1 _) (keyζ _ w _ _ _ hh (spinK a p u s l g M h U).2 _)
omit h
noncomputable def zoneD (Χv:Grid c): Lat.Fields c 6→L[ℂ] Lat.Fields c 6:= mixΛ (fun _=> localF u (gamma g) a a) (fun _=>localF u (gamma g) a a) Χv
local notation "X'"=> localF u (gamma g) a a
local notation "Y'"=> localF (e u) (gamma (s.perm g)) a a
include hp h
lemma dry (X: Lat.Fields c 6): Kit.disguise W (zoneD a u g U' X)=w • zoneD a (e u) (s.perm g) U (Kit.disguise W X):=by
     have hz : X'*W=W*(w • Y'):=by
          have ht:=hp.sends g; cases hr:s.flip g
          · rw [signT,if_neg (by rw[hr]; decide), Complex.ofReal_one,one_smul]; apply w_herd ..; rw [if_neg (by rw[hr]; decide)] at ht; have he:= congr_arg star ht; rw [star_mul,star_mul,gamma_star,gamma_star] at he; exact he.symm
          rw [signT,if_pos hr, Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul]; rw [if_pos hr] at ht; have he:= congr_arg star ht; rw [star_mul,star_mul, star_neg, gamma_star, gamma_star] at he; rw [← show localF (e u) (-gamma (s.perm g)) a a= - Y' from ?_]; apply w_herd ..; exact he.symm
          unfold localF flavorW; rw[TorusPCAC.Geometry.AxisB.opposite]; ext i j; rw [zleft]; simp only [Matrix.neg_apply]; rw [zleft]; split <;> simp -- fill
     change Kit.disguise W (applyMark _ _ X-applyMark _ _ X)= w • (applyMark _ _ (Kit.disguise W X)-applyMark _ _ _); rw [map_sub,smul_sub]; have hh := Lat.copies_unitary 6 V (colour_wheel h hp); exact congr_arg₂ (·-·) (keyζ _ _ _ _ _ hh hz X) (keyζ _ _ _ _ _ hh hz X)
end Oren
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.Oren.meek
#print axioms YM.Massive.PCAC.Oren.dry
