import YM.Oriole.Bent
import YM.Tinus.SpectralB
import YM.Source.Local
import YM.TorusPCAC.Ward.Body
/-! Tally signed moments. Extract pair as REAL finite Body test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC Filter MeasureTheory RG
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)(g:Bool){c:Side}
open Poised.Display Poised.Stative Module Finset Revolve
open SourceRead Patria
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "Cc"=>Modes c 6
local notation "W"=>CensusA d
variable {A B:Type*}[Fintype A][Fintype B]
open Grass.Ward
-- rectangular derivative pairing
lemma sectX (X Y: Matrix A B ℂ) (x: Dirac A): uncoat (adapter X Y x)=Y.transpose*(uncoat x*X):=by
     let P:=adapter X Y; have h(i:B)(x:Dirac A): vary (.inl i) (P x)=∑ j:A,X j i • P (vary (.inl j) x):=by unfold P adapter; rw [QCD.Sway.chain]; simp [Pairs,Fintype.sum_sum_type]
     have he(i:B)(x:Dirac A): vary (.inr i) (P x)= ∑ j:A,Y j i • P (vary (.inr j) x):=by unfold P adapter; rw [QCD.Sway.chain]; simp[Pairs,Fintype.sum_sum_type]
     have hT(y:Dirac A): coef ∅ (P y)=coef ∅ y:= by
          rw [← write y]; simp only [map_sum,map_smul]; refine sum_congr rfl (fun i _ => ?_)
          by_cases h : i=∅
          · subst i; rw [mono_empty,map_one]; rw [show coef (∅:Finset (Pairs A)) 1=1 from TorusPCAC.Ward.zeroR_one,show coef (∅:Finset (Pairs B)) 1=1 from TorusPCAC.Ward.zeroR_one]
          rw [show coef _ (P (mono i))=0 from spectrum (Grass.exterior_layer _ (Grass.homogeneous i)) ∅ (fun e=> h (by rw [← Finset.card_eq_zero]; exact e.symm)),show coef ∅ (mono i)=0 from read_other _ _ (Ne.symm h)]
     ext i j; change - - coef _ (vary _ (vary _ (P x)))= _; rw [he,map_sum,map_sum]; simp_rw [map_smul,h,map_sum,map_smul,hT]; rw [neg_neg,Matrix.mul_apply]; refine sum_congr rfl fun k _=>?_ ; rw [Matrix.mul_apply,mul_sum,smul_eq_mul,mul_sum]; refine sum_congr rfl fun l _=>?_ ; change _= _*(- - coef _ _*_); rw [neg_neg,Matrix.transpose_apply]; simp only [smul_eq_mul,pairD,LinearMap.comp_apply]; ring
variable (p q:Multi d)(i j: Taper) -- wrong var placeholder names.Aside.
variable (H:TaperHol)(h:ℝ)(Y: Pol d) (P X: Density c 6) (D:CensusA d)(T₀:Taper)
local notation "Sp"=> uncoat
local notation "qF" => (Canvas.foil P X) 1
local notation "Qb"=> Sp qF
lemma barren : H.links c d (0:Labels.Jet su) h=1:=by
     funext l; let x:= (Lattice.lift l.1,l.2); have hv:Source.SolvesLink (G:=su) (1:ℝ→su.El) (H.T.connection c d 0 h x):=by
         refine ⟨rfl,fun t=>?_⟩; have hz:H.T.connection c d 0 h x t=0:=by unfold Taper.connection Source.partConnection Source.potential; simp [Labels.Taylor.value,YM.Tensor.diagonal]
         rw [hz, map_zero,mul_zero]; exact hasDerivAt_const _ _
     exact congr_fun ((H.solves ..).unique hv) 1
noncomputable abbrev Np (T₀:Taper)(s:Site c):ℂ:= (T₀.χ ((c.val:ℝ)⁻¹ • vector (Lattice.lift s)) :ℂ)* Cylinder.ap c (Lattice.lift s)
noncomputable abbrev Nw (T₀:Taper)(p:Multi d)(s:Site c) :ℂ:= Np T₀ s * SourceRead.profile p (Lattice.lift s) 1
local notation "Fv"=>H.T.spin (n:=c) (d:=d) h
lemma spin_slot (x:Cc)(u:T): Fv x u=if x.1.2=u.1.2 ∧ x.2=u.2 then (h:ℂ)^spinWeight u.1.1*Nw H.T u.1.1 x.1.1 else 0:=by
     unfold Taper.spin; rw [Matrix.of_apply]; simp only; split_ifs
     · unfold Nw Np SourceRead.profile; simp; ring
     rfl
lemma frac (u v:T) : uncoat (H.test d P X 0 h) u v=(h:ℂ)^(spinWeight u.1.1+spinWeight v.1.1) * ∑ i:Site c,∑ j:Site c, Nw H.T u.1.1 i*Nw H.T v.1.1 j * (Qb ((i,u.1.2),u.2) ((j,v.1.2),v.2)):=by
     unfold TaperHol.test; rw [barren]; change uncoat (adapter _ _ qF) _ _=_; rw [sectX, Matrix.mul_apply]; rw [Fintype.sum_prod_type,Fintype.sum_prod_type,Finset.mul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [sum_eq_single u.1.2]; rw [sum_eq_single u.2]; rw [Matrix.transpose_apply, spin_slot,if_pos ⟨rfl,rfl⟩, Matrix.mul_apply,Fintype.sum_prod_type,Fintype.sum_prod_type, Finset.mul_sum,Finset.mul_sum]; apply sum_congr rfl; intro j _; rw [sum_eq_single v.1.2]; rw [sum_eq_single v.2]; rw [spin_slot,if_pos ⟨rfl,rfl⟩,pow_add]; ring
     · intro a _ h; rw[spin_slot,if_neg (fun z=>h z.2)]; exact mul_zero _
     · simp
     · intro a _ h; apply sum_eq_zero; intro l _; rw[spin_slot,if_neg (fun z=>h z.1),mul_zero]
     · simp
     · intro a _ h; rw[Matrix.transpose_apply,spin_slot,if_neg (fun z=>h z.2),zero_mul]
     · simp
     · intro a _ h; apply sum_eq_zero; intro b _; rw[Matrix.transpose_apply,spin_slot,if_neg (fun z=>h z.1),zero_mul]
     simp
lemma frag (u v:T): uncoat (desired Y 0 h) u v=(h:ℂ)^(spinWeight u.1.1+spinWeight v.1.1)*(juncoat Y u v):=by
     rw [←observe]; unfold observation; rw [LinearMap.comp_apply]; rw [show Source.scaleJet (0:Labels.Jet su) (h^2)=0 from funext fun i=> smul_zero _]; unfold endor; rw [AlgHom.toLinearMap_apply,sectX]; unfold scaled; rw [Matrix.diagonal_transpose,Matrix.diagonal_mul, Matrix.mul_diagonal,pow_add]; change _= _* _* (uncoat (ready d _ _) _ _); ring
variable (μ: UV.Label d)(hH:Tally H 0 μ P X)
include hH
lemma script (u v:T)(hw:spinWeight u.1.1+spinWeight v.1.1≤ d): juncoat μ.val u v=∑ i:Site c,∑ j:Site c, Nw H.T u.1.1 i*Nw H.T v.1.1 j*(Qb ((i,u.1.2),u.2) ((j,v.1.2),v.2)):=by
     let k:= spinWeight u.1.1+spinWeight v.1.1; let f:=H.test d P X (0:Labels.Jet su); let g:=desired μ.val (0:Labels.Jet su); let s: SpinPol d→ₗ[ℂ]ℂ:={toFun:=fun i=> uncoat i u v,map_add':=fun x y=>by rw [map_add]; rfl,map_smul':=fun t y=>by rw[map_smul]; rfl}
     let B:=s.restrictScalars ℝ|>.toContinuousLinearMap
     have he :Agrees f g:= (stamps hH (0:Labels.Jet su)).2; have h:iteratedDeriv k (B∘f) 0=iteratedDeriv k (B∘g) 0:=by rw [clm_step f k _ (he.1.of_le (by exact_mod_cast hw)),clm_step g k _ (he.2.1.of_le (by exact_mod_cast hw)), he.2.2 k hw]
     let Qc:ℂ:= ∑ i:Site c,∑ j:Site c, Nw H.T u.1.1 i*Nw H.T v.1.1 j*(Qb ((i,u.1.2),u.2) ((j,v.1.2),v.2)); let Q:=juncoat μ.val u v
     have hu:B∘f=(fun t:ℝ=> (t^k) • Qc):=funext fun t=> (frac H t P X u v).trans (by rw [← Complex.ofReal_pow]; rfl)
     have hv:B∘g=(fun t:ℝ=>(t^k) • Q):=funext fun t=>(frag t μ.val u v).trans (by rw [← Complex.ofReal_pow]; rfl); rw [hu,hv,iteratedDeriv_smul_const (contDiffAt_id.pow _),iteratedDeriv_smul_const (contDiffAt_id.pow _),iteratedDeriv_fun_pow_zero,if_pos rfl] at h; exact smul_right_injective ℂ (show (k.factorial:ℝ)≠0 from Nat.cast_ne_zero.mpr k.factorial_pos.ne') h.symm
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.script
