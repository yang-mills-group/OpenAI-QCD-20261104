import YM.Heron.Thaw
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Arise.Range
open Maxwell.Free (fromCenter)
open Matrix Finset
variable {d:ℕ} (u:Flavor 6)(i j:Pinor)(a b:Hue)(p q:Multi d)(B:EuPin)(t:Bool)
abbrev PClan:= Flavor 6→ EuPin
noncomputable def tileT (g:PClan)(t:Bool)(d:ℕ) : Matrix (SpinMode d) (SpinMode d) ℂ:= Matrix.of fun i j=> UV.turned (g i.2) (wave (splice t (g i.2))) i j
noncomputable def spun (g:PClan)(d:ℕ) : SpinPol d→ₐ[ℂ]SpinPol d:= Grass.adapter (tileT g false d) (tileT g true d)
variable (g h:PClan)
local notation "T"=> SpinMode d
lemma row_spin (Q:T)(v:T): tileT g t d Q v= UV.turned (g Q.2) (wave (splice t (g Q.2))) Q v:=by unfold tileT; exact Matrix.of_apply .. 
lemma un_spin (Q v:T)(h: Q.2≠v.2) : tileT g t d Q v=0:=by rw[row_spin]; simp only [UV.turned,Matrix.of_apply, if_neg h]
private lemma corridor {α β K M V:Type*}[AddCommMonoid V][Fintype α][Fintype β][Fintype K][Fintype M](f:(α × β× K) × M→ V):∑ i, f i = ∑ i:α,∑ j:β, ∑ k:K,∑ b:M, f ((i,j,k),b):=by rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; exact sum_congr rfl fun _ _=> Fintype.sum_prod_type ..
private lemma oasis (F:T→SpinPol d): ∑ q:T, tileT g t d ((p,i,a),u) q • F q= ∑ q:Multi d,∑ j:Pinor,(multiMove (g u) p q * splice t (g u) i j) • F ((q,j,a),u):=by
     rw [corridor (α:=Multi d) (β:=Pinor) (K:=Hue) (M:=Flavor 6) (fun q=>tileT g t d ((p,i,a),u) q • F q)]; apply sum_congr rfl; intro q _; apply sum_congr rfl; intro j _
     have he(b:Hue): ∑ v:Flavor 6,tileT g t d ((p,i,a),u) ((q,j,b),v) • F ((q,j,b),v)=tileT g t d ((p,i,a),u) ((q,j,b),u) • F ((q,j,b),u):=by rw [sum_eq_single u]; intro i _ h; rw [un_spin t g _ _ (Ne.symm h),zero_smul]; simp
     simp_rw [he]; rw [sum_eq_single a]; rw [row_spin]; simp only[UV.turned,Matrix.of_apply,↓reduceIte,wave,Matrix.kroneckerMap_apply,Matrix.one_apply,ite_mul, mul_ite, ↓reduceIte,mul_one]
     intro b _ h; rw [row_spin]; simp [UV.turned,wave,Matrix.one_apply,h,Ne.symm h]; simp
lemma rolls : spun g d (atom (code t p i a u))= ∑ q:Multi d,∑ j:Pinor, (multiMove (g u) p q * splice t (g u) i j) • atom (code t q j a u):=by
     let F: T:=((p,i,a),u); let X:T→SpinPol d:=fun i=>atom (bond t i); rw [show spun g d (atom (code t p i a u))=∑ q:T,tileT g t d F q • X q from ?_];
     · exact oasis u i a p t g X
     have H(s:PClan)(P:T): spun s d (atom (bond t P))=∑ q:T,tileT s t d P q • atom (bond t q):=by cases t; exact adapt_psi _ _ P; exact adapt_bar _ _ P
     exact H g F
noncomputable def plainPicture (p:EuPin):PClan:= fun _=>p
lemma pictures (s:EuPin)(d:ℕ): spun (plainPicture s) d=UV.twistPins d s:=by unfold spun UV.twistPins; congr 1 <;> (apply Matrix.ext; intros; rfl)
lemma joint_times(p q:EuPin): splice t (p*q)=splice t q* splice t p:=by cases t; change (p.matrix * q.matrix)⁻¹.val=q.matrix⁻¹.val*p.matrix⁻¹.val; rw [_root_.mul_inv_rev]; rfl; exact transpose_mul .. -- inv coer defEq?
end YM.Heron
#print axioms YM.Heron.rolls
