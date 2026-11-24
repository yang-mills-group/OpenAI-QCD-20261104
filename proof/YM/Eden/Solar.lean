import YM.Bloom.Tip
import YM.Next.FREE_KERNELS.Signed
/-! # Genuine invariance of chosen curvature funding (incl harmonic): uniqueness on fields projected to actual curls. -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior FreeResolvent
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free
open scoped Topology BigOperators InnerProductSpace Matrix Classical
variable {G:Gauge}{c f n : Side}{I J V:Type}[Fintype I][Fintype J][Fintype V]
variable (q:Matrix J I ℝ)(M:Matrix J J ℝ){a b:ℝ}(h:Gap M a) (ha:0<a) (hs:M.transpose=M)
include h ha hs
lemma value_unique (Z: Matrix I J ℝ)(hz:R q M * Z=q.transpose): q * Z = copper q M := by
   let U:= holder q M; have he:R q M*U=q.transpose:= holder_value q M h ha
   have ht : (R q M).transpose=R q M:=by rw [R,transpose_mul,transpose_mul, hs,transpose_transpose]; simp only [Matrix.mul_assoc]
   have hx:= congr_arg Matrix.transpose he; rw [transpose_mul,ht,transpose_transpose] at hx
   let P:= R q M; change q * Z=q*U; calc
      q*Z=U.transpose*(P*Z):=by rw [← Matrix.mul_assoc,hx]
      _=U.transpose*(P*U):=by rw [he,hz]
      _=_:=by rw [← Matrix.mul_assoc, hx]
lemma sunlit [DecidableEq I][DecidableEq J] (X:Matrix J J ℝ)(U:Matrix I I ℝ)(hp:X*q=q*U)(ht: U.transpose*R q M*U=R q M)(hm:U*U.transpose=1)(hx:X*X.transpose=1): X*copper q M*X.transpose=copper q M:=by
   unfold copper; rw [← Matrix.mul_assoc, hp]; let R₀:=R q M; let A:=holder q M
   rw [Matrix.mul_assoc, Matrix.mul_assoc]; apply value_unique q M h ha hs
   have hL:R₀*U = U*R₀:=by
        symm; nth_rw 1 [← show U.transpose*R₀*U=R₀ from ht]; rw [← Matrix.mul_assoc U, ← Matrix.mul_assoc U, hm,one_mul]
   have hh := congr_arg Matrix.transpose hp; rw [transpose_mul,transpose_mul] at hh
   change R₀ * (U*(A*X.transpose))= _; rw [← Matrix.mul_assoc,hL,Matrix.mul_assoc,← Matrix.mul_assoc R₀,show R₀*A=q.transpose from holder_value q M h ha,hh, ← Matrix.mul_assoc, hm,Matrix.one_mul]
-- row pay symmetry
omit h ha hs
noncomputable def scoreP (m:I→I)(f:I→ℝ): Matrix I I ℝ := Matrix.of fun i j=> if j=m i then f i else 0
lemma sniper (t:I→I)(b:I→ℝ)(x:I→ℝ): scoreP t b*ᵥ x=fun i=> b i*x (t i):=by funext i; simp [scoreP,mulVec,dotProduct,ite_mul]
lemma peeper (t:I→I)(b:I→ℝ)(G:Matrix I V ℝ) (i j) : (scoreP t b*G) i j=b i*G (t i) j:=by simp [Matrix.mul_apply,scoreP,ite_mul]
lemma shoots (t:I→I)(b:I→ℝ)(G:Matrix V I ℝ)(i j) : (G*(scoreP t b).transpose) i j= G i (t j)*b j:=by simp [Matrix.mul_apply,scoreP,mul_ite]
lemma rays [DecidableEq I] (t:I→I)(b:I→ℝ)(ht:Injective t)(hb:∀ i,b i*b i=1): scoreP t b*(scoreP t b).transpose=1:=by
     ext i j; rw [peeper]; unfold scoreP; simp only [Matrix.of_apply,transpose_apply,Matrix.one_apply,Matrix.of_apply,ht.eq_iff]; by_cases he:i=j<;> simp [he,hb]
-- Planet drift.Proper orientation
variable (s:Signed)
def vertex (s:Signed)(i:Body 1 n):Body 1 n:=let v:=(posDir (axisEquiv.symm i.2)).rotate s; let x:=v.used (affine s 0 i.1); (x.1,coord x.2)
def sig(s:Signed)(i:Body 1 n):ℝ:=let v:=(posDir (axisEquiv.symm i.2)).rotate s; if v.neg then -1 else 1
lemma score_tiltH (x:form 1 n) : scoreP (vertex s) (sig s)*ᵥ x=reorient s x:=by
    funext i; rw [sniper]; unfold reorient vertex sig; dsimp only; split <;> simp
lemma veteran : Injective (vertex (n:=n) s) :=by
     rintro ⟨x,i⟩ ⟨y,j⟩ h; obtain ⟨i,rfl⟩:=axisEquiv.surjective i; obtain ⟨j,rfl⟩:= axisEquiv.surjective j
     have ht : s.perm i=s.perm j:=by
         apply axisEquiv.injective; have hp:=congr_arg Prod.snd h; unfold vertex at hp; simp only [Step.used,Step.rotate,posDir,Bool.false_xor,Equiv.symm_apply_apply] at hp; split at hp <;> split at hp <;> exact hp -- check
     obtain rfl:=s.perm.injective ht; unfold vertex at h; have hx:= congr_arg Prod.fst h; simp only [Step.used,Step.rotate,posDir,Bool.false_xor,Equiv.symm_apply_apply] at hx
     cases he:s.flip i <;> simp only [he,↓reduceIte,Bool.false_eq_true,sub_left_inj] at hx <;> simp [affine] at hx <;> rw [s.act_injective hx]
-- plaquette convention
noncomputable def hat (s:Signed)(n:Side): Equiv.Perm (Body 2 n):= (address n).symm.trans ((regime s n).trans (address n))
noncomputable def paint(s:Signed)(i:Body 2 n) := turned s ((address n).symm i).2
lemma arena : scoreP (hat s n) (paint s)*d 1 n=d 1 n*scoreP (vertex s) (sig s):=by
    let X:Matrix (Body 2 n) (Body 2 n) ℝ:= scoreP (hat s n) (paint s); let Q:Matrix (Body 2 n) (Body 1 n) ℝ:=d 1 n; let Z:=scoreP (vertex s) (sig (n:=n) s); change X*Q=Q*Z; apply Matrix.ext_of_mulVec_single; intro v; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; unfold X Q Z; rw [sniper,score_tiltH]; funext i; obtain ⟨⟨x,a⟩,rfl⟩:= (address n).surjective i; unfold hat paint; simp only [Equiv.symm_apply_apply, Equiv.trans_apply]; exact (rotations_d _ _ _ _).symm
variable (H: Bed)(t : Clip)
local notation "Mq"=> H.metric.acts n
local notation "Q"=> learned H n
open Bid
lemma repricer (u:G.ColorIndex)(hf:Bid.Sworn H n G) : let U:=scoreP (vertex s) (sig (n:=n) s); U.transpose*R (d 1 n) Mq*U = R (d 1 n) Mq:=by
     intro U; let X:=R (d 1 n) Mq; let Q':= Precision.K Mq; have h(p q:form 1 n) : dotProduct (U*ᵥ p) (Q'*ᵥ(U*ᵥ q))= dotProduct p (Q'*ᵥ q):=by
          let A(p:form 1 n) : Dir G n:=fun i=> EuclideanSpace.single u (p i)
          have hx (p:form 1 n) (i:G.ColorIndex): parts G 1 (A p) i=if i=u then p else 0:=by funext x; by_cases ht:i=u <;> simp [A, parts, ht]
          have ht:=hf s (A p) (A q); unfold gaugeFiscal at ht; simp_rw [pigment,hx,← score_tiltH] at ht; rw [Finset.sum_eq_single u,Finset.sum_eq_single u] at ht; simp only [if_true] at ht; exact ht -- obligations order
          all_goals simp_all -- try
     -- convert Q
     apply Matrix.ext_of_mulVec_single; intro i; funext j; let x:= (Pi.single j 1:form 1 n); let y:=(Pi.single i 1:form 1 n); have he := h x y; rw [← vecMul_transpose,← dotProduct_mulVec] at he; change _= _ at he; rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec] at he; have HE:Q'=X:=rfl; rw [HE] at he; simpa [x,y,dotProduct,Pi.single_apply, ite_mul] using he
lemma luminous (x y:Face (Per n))(h:Floor H t n a b)(ha:0<a)(hf: Bid.Sworn H n G)(u:G.ColorIndex): turned s x.2 * Q (address n (regime s n x)) (address n (regime s n y))*turned s y.2=Q (address n x) (address n y):=by
    have hu : let U:=scoreP (vertex s) (sig (n:=n) s); U*U.transpose=1:=by intro U; exact rays _ (sig s) (veteran s) fun (i:Body 1 n)=>by unfold sig; dsimp only; split <;> norm_num
    have hx : let X:=scoreP (hat s n) (paint s); X*X.transpose=1:=by intro U; exact rays _ (paint s) ((hat s n).injective) (fun i=>turned_sq ..)
    have he:= sunlit (d 1 n) Mq ⟨fun v=> (h.uniform.1 v).1⟩ ha h.symmetric.1 _ _ (arena s) (repricer s H u hf) hu hx; change _* Q *_=Q at he; have hg:= congr_fun (congr_fun he (address n x)) (address n y); rw [shoots,peeper] at hg; simp only [paint,hat,Equiv.symm_apply_apply, Equiv.trans_apply] at hg; exact hg
end YM.Eden
#print axioms YM.Eden.value_unique
#print axioms YM.Eden.luminous
