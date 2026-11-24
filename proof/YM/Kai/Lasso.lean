import YM.Kai.Creep
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth
open Entr Entr.Meridian Stew
open QCD.Tide
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}
open Revolve TorusPCAC.Geometry.Switch TorusPCAC.Geometry.AxisB
variable {A:Type*} [Fintype A]
-- change by leaf.F.G
lemma charge_shiftM (v:Bool)(L R M M':Sour A)(h:M*L=L*M'.transpose)(hr:R.transpose*M'=M.transpose*R.transpose)(x:Dirac A): shiftC L R (applyMark v M x)= applyMark (!v) M' (shiftC L R x):=by
     let f:= shiftC L R; let t:= applyMark v M; let w:=applyMark (!v) M'
     suffices h:∀ i:Pairs A, f (t (atom i))=w (f (atom i)) by
         have H(s:List (Pairs A)): f (t (s.map atom).prod)=w (f (s.map atom).prod):=by
             induction s with
             | nil=>simp [f,t,w,L_one]
             | cons i s ih=> simp only[List.map_cons,List.prod_cons]; change f (applyMark _ _ (atom i*_))=applyMark _ _ (f (atom i*_)); rw [map_mul f,LMark,LMark,map_add,map_mul f,map_mul f]; change f (t (atom i))*_+_ * f (t _) = w _ * _+ _ * w _; rw[h,ih]
         have he (s:Finset (Pairs A)): f (t (mono s))= w (f (mono s)):=by obtain ⟨q,-,-,hp⟩:=expression s; rw[hp]; simpa only[List.map_ofFn] using H (List.ofFn q)
         change f (t x)=w (f x); rw [←write x]; simp_rw[map_sum,map_smul,he]
     intro i; have hw(i j:A): (∑ k:A,-R k i * M' k j)= ∑ k:A,M k i * -R j k:=by -- wait equation. bar case. derive
          -- bar source B: t true bar i = ∑ M k i bar k ; f then = −M k i*R j k; w: applyMark false M' ψ j => − R k i * M' k j . Requirement transpose? ∑ R k i M' k j = M k i R j k => Rᵀ*M' = Mᵀ*Rᵀ.
          have hx:=congr_fun (congr_fun hr i) j; simp_rw [neg_mul,mul_neg,sum_neg_distrib]; apply congr_arg Neg.neg; exact hx -- orientation
     rcases i with i|i
     · cases v
       · change shiftC L R (applyMark false M (psi i))= applyMark true M' (shiftC L R (psi i)); rw [leftP,chant_psi,map_sum,map_sum]; simp_rw [map_smul,chant_psi,leftB,smul_sum,smul_smul]; rw[sum_comm]; conv_rhs=> rw[sum_comm]
         refine sum_congr rfl fun k _=> ?_; rw [←sum_smul,←sum_smul]; exact congr_arg (· • bar k) (congr_fun (congr_fun h i) k) -- h orientation
       change shiftC L R (applyMark true M (psi i))= applyMark false M' (shiftC L R (psi i)); rw[passP,map_zero,chant_psi,map_sum]; simp_rw [map_smul,passB,smul_zero,sum_const_zero]
     cases v
     · change shiftC L R (applyMark false M (bar i))=applyMark true M' (shiftC L R (bar i)); rw [passB,map_zero,chant_bar,map_sum]; simp_rw[map_smul,passP,smul_zero,sum_const_zero]
     change shiftC L R (applyMark true M (bar i))=applyMark false M' (shiftC L R (bar i)); rw [leftB,chant_bar,map_sum,map_sum]; simp_rw[map_smul,chant_bar,leftP,smul_sum,smul_smul]; rw[sum_comm]; conv_rhs=>rw[sum_comm]
     refine sum_congr rfl fun k _=> ?_; rw [←sum_smul,←sum_smul, hw]
-- requirement hv: R?... M'=transp (R*M*L); if M*L=L*M'T ; charge on true bar wants Rᵀ*M'? compute with R*L=1: M'=Lᵀ*Mᵀ*Rᵀ gives Rᵀ*M'=Mᵀ*Rᵀ ; yes.
variable (a: Flavor 6)(p:Site c)(i:Axis)(U:Grid c)
open TorusPCAC.Jet TorusPCAC.Spin TorusPCAC.Jet.Selector
local notation "S"=> TorusPCAC.Stencil.conjGrid U
local notation "L"=> Jobs c 6 Cmat
local notation "H"=> Jobs c 6 Cmat⁻¹
local notation "Z"=> zone 6 p
lemma ceil_zero(M:Spike): Commute (Jobs c 6 M) (zone 6 p):=by
     -- focus diag
     unfold Commute SemiconjBy
     ext i j; rw [zright,zleft]; by_cases he:i.1.1=j.1.1; · rw [he]
     have hp: Jobs c 6 M i j=0:=by 
         unfold Jobs copies; rw [Matrix.blockDiagonal_apply]; split; · simp [onSpin,rides,he]
         rfl
     rw[hp,ite_self,ite_self]
lemma κlease (A D: Sour (Modes c 6))(h:(H*A*L).transpose=D)(v:Bool)(x:Lat.Fields c 6): TorusPCAC.Stencil.charge c (applyMark v A x)= applyMark (!v) D (TorusPCAC.Stencil.charge c x):=by
     have hu: H*L=1:=pay _ _ pays_C
     have hv: L*H=1:=pay _ _ pays_C'
     unfold TorusPCAC.Stencil.charge; simp_rw [shifted]; refine charge_shiftM _ _ _ _ D ?_ ?_ _
     · rw[← h, Matrix.transpose_transpose,←Matrix.mul_assoc, ←mul_assoc L, hv,one_mul] -- exact
     rw[← h]; simp only [Matrix.transpose_mul]; rw[←mul_assoc,← Matrix.transpose_mul,hv,Matrix.transpose_one,one_mul]
lemma δc : (delta S i).transpose= -delta U i:=by
     unfold Stew.delta; rw [twist_shift, Matrix.transpose_smul, Matrix.transpose_sub, show (Lat.shift (0:Site c) _ _)=_ from rfl]; simp only [Twist,Matrix.transpose_transpose]; rw [show (star _)ᵀ=Lat.shift 0 U i from ?_]; rw [← smul_neg, neg_sub]; rfl
     exact twist_turn _ -- check path
lemma κZ : (Z).transpose= Z:=by unfold zone; rw [Matrix.diagonal_transpose]
lemma spotT : (spot a a).transpose=spot a a:=by ext i j; simp [spot,and_comm]
local notation "X"=> keel p i a S
local notation "X'"=> keelB p i a S
local notation "Y"=> keel p i a U
local notation "Y'"=> keelB p i a U
lemma yard : Commute ((delta U i) ⊗ₖ spot a a) L:=by
     unfold Commute SemiconjBy; rw[show L=onSpin c _ ⊗ₖ 1 from QCD.Sway.choir_in ..]; rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, (Stew.Δ_spins ..).eq,mul_one,one_mul]
lemma bKeel : (H*X*L).transpose= - Y' ∧ (H*X'*L).transpose=-Y:=by
     let Q:= delta S i ⊗ₖ spot a a; let Q':=delta U i ⊗ₖ spot a a; have hu: H*L=1:=pay _ _ pays_C; have hh: Commute (keel p i a S) L:= (ceil_zero p _).symm.mul_left (yard a i S); have hz: Commute (keelB p i a S) L:= (yard a i S).mul_left (ceil_zero p _).symm
     have hv: Q.transpose= - Q':=by change Matrix.kronecker (delta S i).transpose (spot a a).transpose=_; rw[δc i U,spotT]; simp [Lat.kron_neg,Q']
     rw [mul_assoc H _,hh.eq, ← mul_assoc H,hu,one_mul,mul_assoc H _,hz.eq,←mul_assoc H,hu,one_mul]; change (Z*Q).transpose= - (Q'*Z) ∧ (Q*Z).transpose= -(Z*Q'); rw [Matrix.transpose_mul,Matrix.transpose_mul,hv,κZ,Matrix.neg_mul,Matrix.mul_neg]; exact ⟨rfl,rfl⟩
local notation "T"=> localF p (gamma i) a a
lemma b_zone(N:Spike)(h:(Cmat⁻¹*N*Cmat).transpose=N) : (H*localF p N a a*L).transpose=localF p N a a:=by -- Z entry positive if scalar
     rw[localF, ← Matrix.mul_assoc, (ceil_zero ..).eq]; unfold flavorW; rw [show H=onSpin c Cmat⁻¹ ⊗ₖ 1 from QCD.Sway.choir_in .., show L=onSpin c Cmat ⊗ₖ 1 from QCD.Sway.choir_in ..]; rw [Matrix.mul_assoc Z,Matrix.mul_assoc Z,← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Lat.on_spin_mul,Lat.on_spin_mul, mul_one,one_mul, Matrix.transpose_mul,κZ]; change ((onSpin c (Cmat⁻¹*N*Cmat)).transpose ⊗ₖ (spot a a).transpose)*Z=_; rw[← on_spin_trans,h,spotT]; exact (commute_here a a p N).eq.symm
lemma b_gamma : (H*T*L).transpose= - T:=by
     unfold localF; rw[← Matrix.mul_assoc, (ceil_zero ..).eq]; unfold flavorW; rw [show H=onSpin c Cmat⁻¹ ⊗ₖ 1 from QCD.Sway.choir_in .., show L=onSpin c Cmat ⊗ₖ 1 from QCD.Sway.choir_in ..]; rw [Matrix.mul_assoc Z,Matrix.mul_assoc Z,← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,Lat.on_spin_mul,Lat.on_spin_mul,mul_one,one_mul, Matrix.transpose_mul,κZ]; change ((onSpin c (Cmat⁻¹*gamma i*Cmat)).transpose ⊗ₖ (spot a a).transpose)*Z=_; rw [← on_spin_trans,moves_C,spotT,TorusPCAC.Geometry.AxisB.opposite,Lat.kron_neg,Matrix.neg_mul]; exact congr_arg Neg.neg (commute_here a a p _).eq.symm
lemma cStars (x:Lat.Fields c 6) : let T_:= TorusPCAC.Stencil.charge c (N:=6); T_ (beacon a p i S x)=beacon a p i U (T_ x) ∧ T_ (zoneD a p i S x)=zoneD a p i U (T_ x):=by
     intro t; constructor
     · change t (applyMark _ _ x-applyMark _ _ x)= applyMark _ _ (t x) - applyMark _ _ _; have hY:= κlease X (-Y') (bKeel a p i U).1 false x; have hx:=κlease X' (-Y) (bKeel a p i U).2 true x; unfold t; rw [map_sub,hx,hY,← neg_one_smul ℂ (Y'),←neg_one_smul ℂ (Y),scales _ _ Y',scales _ _ Y]; simp; abel
     change t (applyMark _ _ x - applyMark _ _ x)= applyMark _ _ _ - applyMark _ _ _; unfold t; rw [map_sub,κlease T (-T) (b_gamma a p i) false x,κlease T (-T) (b_gamma a p i) true x,←neg_one_smul ℂ T,scales _ _ T,scales _ _ T]; simp; abel
end YM.Massive.PCAC.Oren
#print axioms YM.Massive.PCAC.Oren.bKeel
