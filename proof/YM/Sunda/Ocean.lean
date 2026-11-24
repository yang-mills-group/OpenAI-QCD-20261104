import YM.Sunda.Loft
import YM.Sunda.Chroma
import YM.Affina.Pearls
set_option maxHeartbeats 540000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open Massive.Patria.Gall Massive.Patria.Gall.Onyx Massive.Tarn.ChargeQ
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
variable {ρ:EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
set_option quotPrecheck false
local notation "X0"=> equip T ρ A.jet
open Sunda Lobo
open Massive.Oriole Compass MassFields Signals
variable (y:Bool)(k:Tri)
noncomputable def matP (y:Bool)(p:EuPin):ℂ:=if y then (orient p:ℂ) else 1
lemma mat1 : matP y 1=1:=by cases y<;>simp[matP]
lemma matM (p z:EuPin): matP y (p*z)=matP y p * matP y z:=by cases y<;>simp [matP]
lemma pulpP(p:EuPin): Oriole.conjug p (pulp y)=matP y p • pulp y:=by
     cases y; · change Oriole.conjug _ 1=(1:ℂ) • (1:Spike); unfold Oriole.conjug; rw [one_smul,mul_one]; exact p.matrix.val_inv
     exact violet _
lemma foxW(p:EuPin)(s:Signed)(hs:p.Lifts s)(i:Axis): Oriole.conjug p (claw y i)=((signT s i:ℂ)*matP y p) • claw y (s.perm i):= claw_pin y s p i hs _ (pulpP y p)
lemma yawA(t:ℝ): matP y (pathW k t)=1:=by cases y<;> simp[matP,violet_path]
lemma holy (k:Tri) : ∃ s:Signed,(pathW k (Real.pi+Real.pi/2)).Lifts s:=by
     obtain ⟨s,hs⟩:=headed k; refine ⟨s*Cup k,?_⟩; rw [SpinParity.additive (treks k)]; change euca (pathW k Real.pi*SpinQ k)= Signed.inclusionO (s*Cup k); rw [map_mul,map_mul, show euca _=_ from hs, show euca (SpinQ k)=_ from fL k]; rfl -- placeholder
variable (e:Axis→K.W)(x:K.W)
noncomputable def feeD(p: EuPin)(e:Axis→K.W)(i:Axis):K.W:=matP y p • ∑ j:Axis,(p.coord.val j i:ℂ) • e j
lemma feOne(i:Axis): feeD y 1 e i=e i:=by unfold feeD; rw [mat1,one_smul]; change ∑ j:Axis,(↑((1:M4) j i):ℂ) • e j=_; simp [Matrix.one_apply,apply_ite Complex.ofReal,ite_smul]
lemma feMul(p q:EuPin)(i:Axis): feeD y (p*q) e i= matP y q • (∑ j:Axis,(q.coord.val j i:ℂ) • feeD y p e j):=by
     unfold feeD; rw [matM, show (p*q).coord.val=p.coord.val*q.coord.val from rfl]; simp_rw [Matrix.mul_apply, Complex.ofReal_sum,Finset.smul_sum, Finset.sum_smul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; -- smul outer currently over ∑ via simp_rw not second nested after first?
     simp_rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; simp_rw [Complex.ofReal_mul, smul_smul]; module
lemma feeSign (p:EuPin)(s:Signed)(hs:p.Lifts s)(i:Axis):feeD y p e i=((↑(signT s i):ℂ)*matP y p) • e (s.perm i):=by
     unfold feeD; rw[show p.coord.val=s.matrix from congr_arg Subtype.val hs, Finset.sum_eq_single (s.perm i)]; · simp only [Signed.matrix_at,if_pos rfl]; change matP y p • ((↑(signT s i):ℂ) • _) = _; rw [smul_smul,mul_comm]
     · intro j _ hj; rw [Signed.matrix_at,if_neg (Ne.symm hj),Complex.ofReal_zero,zero_smul]
     simp
lemma fePath (i:Axis) : (fun t=>feeD y (pathW k t) e i)∈Uno K.W:=by
     have ht(t:ℝ) : feeD y (pathW k t) e i=palm k t e i:=by rw [feeD,yawA,one_smul,(treks k).2.2]; rfl
     rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩|rfl
     · refine Eq.subst (motive:=fun f:ℝ→ K.W=>f∈Uno K.W) (funext (show ∀ t:ℝ,feeD y (pathW k t) e (lieu i)=wing k t (e ∘lieu) i from fun t=> (ht t).trans (hat ..))).symm (Sunda.chord ..)
     exact Eq.subst (motive:=fun f:ℝ→K.W=>f∈ Uno K.W) (funext (show ∀ t:ℝ,feeD y (pathW k t) e timeAxis=e timeAxis from fun t=>(ht t).trans (lastB ..))).symm (univoc _)
include J H JQ S B R
lemma incline (i:Tri)(x:K.W)(hx:x∈K.level 8)(f:ℝ→K.W)(hf:f∈Uno K.W)(h0:x=f 0)(he:∀ t:ℝ,(∃ s:Signed,(pathW i t).Lifts s)→ρ (pathW i t) x=f t)(t:ℝ): ρ (pathW i t) x=f t:=by
     have hp:= he (Real.pi/2) ⟨Cup i,fL i⟩; have hv:= he Real.pi (headed i)
     refine congr_fun (Sunda.known (lows J H JQ B R S i x hx ?_) f hf ?_ hp hv) t; · rw [hp,hv,he _ (holy _)]; nth_rw 1 [h0]; simpa only [zero_add] using (echoes hf 0)
     rw [(treks i).1,map_one]; exact h0
lemma legitimate (h:∀ (p:EuPin)(s:Signed),p.Lifts s→ρ p x= matP y p • x)(hx:x∈K.level 8): properScalar (equip T ρ A.jet) x:=by
     let i:Tri:= 0; let U: Subgroup EuPin:={
           carrier:={t|ρ t x=matP y t • x}
           one_mem':=by simp [mat1]
           mul_mem':=by
                intro p q (hp:ρ p x=matP y p • x)(hq:ρ q x=matP y q • x); change ρ (p*q) x=_; rw [map_mul, LinearEquiv.mul_apply,hq,map_smul,hp,matM,smul_smul,mul_comm]
           inv_mem':=by
                intro p (hp:ρ p x=matP y p • x); apply (ρ p).injective; rw [map_inv,map_smul,hp, smul_smul, ←matM, inv_mul_cancel,mat1,one_smul]; exact (ρ p).apply_symm_apply _ }
     intro t ht; have hv:t∈U:=by
          apply genreK i U h; intro k; change ρ (pathW i k) x=_; rw [yawA,one_smul]; refine incline J H JQ B R S i x hx (fun _=>x) (univoc _) rfl ?_ k; rintro r ⟨s,hs⟩; rw[h _ s hs, yawA,one_smul]
     change ρ t x=x; change ρ t x=matP y t • x at hv; rw[hv]; cases y <;> simp [matP, show orient t=1 from ht]
lemma earnsV (h:∀ (p:EuPin)(s:Signed),p.Lifts s→∀ i:Axis,ρ p (e i)= feeD y p e i)(he:∀ i:Axis,e i∈ K.level 8): properVector (equip T ρ A.jet) e:=by
     let V(p:EuPin):Prop:=∀ i:Axis,ρ p (e i)= feeD y p e i; let i:Tri:=0; let U:Subgroup EuPin:={
           carrier:= {t| V t}
           one_mem':=fun x=>by rw[feOne,map_one]; rfl
           mul_mem':=by
                intro v t (hv:V v)(ht:V t) x; rw[map_mul,LinearEquiv.mul_apply,ht,feMul]; unfold feeD; rw [map_smul,map_sum]; apply congr_arg; refine Finset.sum_congr rfl fun j _=>?_ ; rw [map_smul,hv]; rfl
           inv_mem':=by
                intro v (hv:V v) x; apply (ρ v).injective; rw [← LinearEquiv.mul_apply,←map_mul,mul_inv_cancel,map_one]; calc
                    _ = feeD y (v*v⁻¹) e x:=by rw[mul_inv_cancel, feOne]; rfl
                    _ = _ :=by rw [feMul]; nth_rw 1 [show (ρ v) (feeD y v⁻¹ e x)= (ρ v) (matP y v⁻¹ • (∑ j:Axis, ((v⁻¹).coord.val j x:ℂ) • e j)) from rfl,map_smul,map_sum]; apply congr_arg; refine Finset.sum_congr rfl fun j _=>?_ ; rw [map_smul,hv] }
     intro j p hp; have hP:p∈U:=by
           apply genreK i U h; intro k x; exact incline J H JQ B R S i (e x) (he x) _ (fePath y i e x) (by rw [(treks i).1,feOne]) (fun t ⟨s,hs⟩=> h _ s hs x) k -- cannot fun pattern Exists?
     change ρ p (e j)=_; rw [(show V p from hP) j]; unfold feeD; have hv:matP y p=1:=by cases y<;> simp[matP, show orient p=1 from hp]
     rw[hv,one_smul]
end YM.Mako
#print axioms YM.Mako.legitimate
#print axioms YM.Mako.earnsV
#print axioms YM.Mako.foxW
