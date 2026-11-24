import YM.Gust.Pear
import YM.Oriole.Indigo
import YM.MassiveTwoEstimates.SpinGeometry
set_option maxHeartbeats 440000
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV
open Function Matrix Finset QCD QCD.Lat Lattice QCD.Grass TensorProduct
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ComplexOrder TensorProduct Kronecker Classical
variable {d:ℕ}(a b:Axis)(p:EuPin)(hh:p.Lifts (Signed.mirror a))(hx:p.matrix.val = -Complex.I • (gamma a*g5))
local notation "G"=> g5
local notation "T"=> SpinMode d
include hx
lemma chaos :star p.matrix.val= p.matrix.val:=by rw[hx,star_smul,star_mul,g5_star,gamma_star,star_neg,show star (Complex.I:ℂ)=_ from Complex.conj_I, neg_neg,show g5*gamma a= -(gamma a*g5) from by rw[five,neg_neg],smul_neg,neg_smul]
local notation "M"=> p.matrix.val
local notation "R"=> p.matrix⁻¹.val
lemma key0: (-(gamma a).transpose) * (M).transpose= -Complex.I • g5.transpose:=by
       rw[Matrix.neg_mul,← transpose_mul,hx,Matrix.smul_mul, show gamma a*g5*gamma a= -g5 from ?_,transpose_smul,transpose_neg,smul_neg,neg_neg];rw [five a,neg_mul, Matrix.mul_assoc,gamma_sq,mul_one]
lemma key1: -(gamma a)*R=Complex.I • g5:=by
       rw [Oriole.E_star,chaos a p hx,hx,Matrix.neg_mul,Matrix.mul_smul,← Matrix.mul_assoc,gamma_sq,one_mul,neg_smul,neg_neg]
omit hx
abbrev Sigma5(d:ℕ): Matrix (Pairs (SpinMode d)) (Pairs (SpinMode d)) ℂ := fromBlocks 0 (spinTable (-Complex.I • g5.transpose)) (spinTable (Complex.I • g5)) 0
abbrev darkR(d:ℕ) : Pol d →ₛₗ[starRingEnd ℂ] Pol d:= TensorProduct.map conjGPol ((changeVars (Sigma5 d)).toLinearMap.comp dagger)
include hx hh
lemma rooted (X:Pol d): pinAct p (UV.adj a X)=darkR d X:=by
   induction X using TensorProduct.induction_on with
   | zero=> simp
   | add x y h k=> simp only [map_add,h,k]
   | tmul x y=> unfold pinAct UV.adj darkR; simp_rw[TensorProduct.map_tmul]; apply congr_arg₂ (tmul ℂ)
                · change Labels.rotated p.coord (Labels.rotated _ _)=_; rw [← Labels.rotation_law,show p.coord=Signed.reflect a from hh,show Signed.reflect a *Signed.reflect a=1 from ?_]; exact burns _; change Signed.inclusionO _* Signed.inclusionO _= _; rw [← map_mul Signed.inclusionO,show Signed.mirror a* Signed.mirror a=1 from inv_mul_cancel _,map_one]
                let X:= Matrix.fromBlocks (turned (d:=d) p (wave R)) 0 0 (turned (d:=d) p (wave (M).transpose)); change changeVars X (changeVars (eyeW _ _) (dagger y))=changeVars (Sigma5 d) (dagger y); rw [multipleChange]; congr 1; unfold X eyeW Sigma5; rw [← hem_turn _ hh,←hem_turn _ hh,fromBlocks_multiply,glimmer,glimmer,key0 _ _ hx,key1 _ _ hx]; simp
omit hh hx
-- key algebra K p = parity factor times p K for each generator (K conjugation improper). exponent works on shared tag.
noncomputable def tauMod (b:Bool) :ℂ:= if b then -1 else 1
lemma chi_spec(s:Signed)(hs:p.Lifts s):∃ b:Bool,p.matrix.val*g5=tauMod b • (g5*p.matrix.val):=by
    obtain ⟨c,hc⟩:= Oriole.chirP true s p hs; obtain hor|hop := mul_self_eq_one_iff.mp ((Oriole.p_mag true p c hc).2)
    · refine ⟨false,?_⟩; change M*g5*R=c • g5 at hc; have h:=congr_arg (· * M) hc; rw[Matrix.mul_assoc _ R,Oriole.inv2,mul_one,hor,one_smul] at h; simpa [tauMod] using h
    · refine ⟨true,?_⟩; change M*g5*R=c • g5 at hc; have h:=congr_arg (· * M) hc; rw[Matrix.mul_assoc _ R,Oriole.inv2,mul_one,hop,neg_one_smul,Matrix.neg_mul] at h; simpa[tauMod] using h
local notation "Seq"=> fromBlocks (turned (d:=d) p (wave R)) 0 0 (turned (d:=d) p (wave (M).transpose))
lemma tmodStar (A:Spike): Mstar (turned (d:=d) p (wave A))= turned p (wave (Mstar A)) :=by
      ext i j; simp only [turned,Mstar,of_apply,Matrix.map_apply]; split
      · rw[map_mul]; congr 1; · exact row_star ..
        exact congr_fun (congr_fun (mstar_wave A) i.1.2) j.1.2
      rw [map_zero]
lemma vSM(t:EuPin)(A:Spike)(c:ℂ): turned (d:=d) t (wave (c • A))= c • turned t (wave A) :=by ext i j; unfold Lat.wave UV.turned; by_cases h:i.2=j.2 <;> simp [h,mul_assoc,mul_left_comm]
include d
lemma roarZ (u:Bool)(hu:M*G=tauMod u • (G*M)): Mstar (Seq)*Sigma5 d= tauMod u • (Sigma5 d*(Seq)):=by
      let a:= (-Complex.I) • Gᵀ; let b:= Complex.I • G
      let x: Matrix T T ℂ:=turned p (wave R); let y:Matrix T T ℂ:=turned p (wave (Mᵀ)); change Mstar (fromBlocks x 0 0 y)*fromBlocks 0 (spinTable a) (spinTable b) 0=tauMod u • (fromBlocks 0 _ _ 0*fromBlocks x 0 0 y)
      rw[mstar_diag,fromBlocks_multiply,fromBlocks_multiply]; simp only[Matrix.zero_mul,Matrix.mul_zero, add_zero,zero_add]; unfold x y; simp_rw[under_spin,tmodStar,reel, one_mul,mul_one,wave_mul];
      have h:Mstar R=Mᵀ:=by rw[mstar_sq,Oriole.E_star,star_star];
      have ht: (Mstar R)*a=tauMod u • (a*Mᵀ):=by
         rw[h]; have hh:tauMod u • (M*g5)=g5*M:=by rw[hu, smul_smul]; cases u <;>simp[tauMod]
         rw[show Mᵀ*a=(-Complex.I) • (G*M)ᵀ from ?_,← hh,transpose_smul,smul_comm]; unfold a; rw[Matrix.smul_mul,←transpose_mul] -- verify it's M*g transpose.M
         unfold a; rw [Matrix.mul_smul,← transpose_mul]
      have hV:Mstar (Mᵀ)*b=tauMod u • (b*R):=by
         have hh:R*g5= tauMod u • (g5*R):=by rw [Oriole.E_star]; have h:=congr_arg star hu; rw [star_mul,g5_star,star_smul,star_mul,g5_star] at h; rw [h,smul_smul]; cases u <;>simp[tauMod]
         rw [show Mstar Mᵀ= R from Oriole.E_star p|>.symm]; unfold b; rw [Matrix.mul_smul,hh,Matrix.smul_mul,smul_comm]
      rw [ht,hV,vSM,vSM]; ext (i|i) (j|j)<;> simp[a,b]
lemma sign_act (A:Matrix (Pairs T) (Pairs T) ℂ) (X:Dirac T):changeVars (-A) X=Grass.grade (changeVars A X):=by
     have h:changeVars (-(1:Matrix (Pairs T) (Pairs T) ℂ))=Grass.grade:=by apply QCD.Grass.ext_atoms; intro i; rw[change_atom,grade_atom]; simp [Matrix.one_apply]
     rw [←h,multipleChange, Matrix.mul_neg,mul_one]
lemma rotateC(u:Bool)(h:M*g5=tauMod u • (g5*M))(x:Pol d):darkR d (pinAct p x)=(if u then parityAct (pinAct p (darkR d x)) else pinAct p (darkR d x)):=by
     induction x using TensorProduct.induction_on with
     | zero=>split <;> simp
     | add x y hx hy=> cases u <;> simp_all only[map_add,↓reduceIte,Bool.false_eq_true]
     | tmul x y=>
          have hx : conjGPol (Labels.rotated p.coord x)= Labels.rotated p.coord (conjGPol x):=(conj_mobil ..).symm
          cases u
          · rw [if_neg (by decide)]; unfold darkR pinAct; simp_rw[TensorProduct.map_tmul]; apply congr_arg₂ (tmul ℂ); · exact hx
            change changeVars (Sigma5 d) (dagger (changeVars (Seq) y))=changeVars (Seq) (changeVars (Sigma5 d) (dagger y));rw[dagger_change,multipleChange,multipleChange,roarZ p false h];simp[tauMod]
          · rw [if_pos rfl]; unfold darkR pinAct parityAct; simp_rw [TensorProduct.map_tmul]; apply congr_arg₂ (tmul ℂ)
            · exact hx
            · change changeVars (Sigma5 d) (dagger (changeVars (Seq) y))= Grass.grade (changeVars (Seq) (changeVars (Sigma5 d) (dagger y))); rw[dagger_change,multipleChange,multipleChange,roarZ p true h,show tauMod true=(-1:ℂ) from rfl,neg_one_smul]; exact sign_act ..
end YM.Massive.UV
#print axioms YM.Massive.UV.rooted
#print axioms YM.Massive.UV.rotateC
