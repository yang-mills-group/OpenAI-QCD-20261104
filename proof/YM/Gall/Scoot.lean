import YM.Gall.Dial
/-! Symmetry of exact-gradient compensation, polynomial bounds in lattice distance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace Interval
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p w:ℕ}
local notation "Y★"=> Cray c
noncomputable abbrev peg (x:Site c)(d:ℕ):ℝ:= (1+(pdist x:ℝ))^d
lemma peg_p (x:Site c)(k m:ℕ)(hk:k ≤ m): 1 ≤ peg x k∧peg x k ≤ peg x m:= ⟨one_le_pow₀ (by simp),pow_le_pow_right₀ (by simp) hk⟩
lemma pin_peg (x:Site c)(m:ℕ):0 < peg x m:=zero_lt_one.trans_le (peg_p x m _ le_rfl).1
noncomputable abbrev Dart (p:ℕ)(F:∀ c:Side,Cray c):Prop:=∃ C:ℝ,0≤C∧∀ (c:Side)(e:Edge (Site c)), ‖F c e‖ ≤ C*peg e.1 p
variable {F H: ∀ c:Side, Cray c}
lemma dart_plus (h:Dart p F)(hp:Dart p H):Dart p (F+H):=by obtain ⟨f,hf,he⟩:=h; obtain ⟨g,hg,hu⟩:= hp; exact ⟨f+g,add_nonneg hf hg,fun i j=> (norm_add_le ..).trans ((add_le_add (he i j) (hu i j)).trans_eq (add_mul ..).symm)⟩
lemma dart_sub (h:Dart p F)(hp:Dart p H): Dart p (F-H):=by obtain ⟨f,hf,he⟩:=h; obtain ⟨g,hg,hu⟩:= hp; exact ⟨f+g,add_nonneg hf hg,fun i j=> (norm_sub_le ..).trans ((add_le_add (he i j) (hu i j)).trans_eq (add_mul ..).symm)⟩
lemma dart_smul (h:Dart p F)(t:ℝ): Dart p (t • F):=by obtain ⟨f,hf,he⟩:=h; refine ⟨‖t‖ * f,mul_nonneg (norm_nonneg _) hf,fun i j=>?_⟩; rw [Pi.smul_apply,Pi.smul_apply,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (he ..) (norm_nonneg _)
lemma dart_weaker (h:Dart p F)(hp:p ≤ m): Dart m F:=by obtain ⟨f,hf,he⟩:=h; exact ⟨f,hf,fun i j=> (he ..).trans (mul_le_mul_of_nonneg_left (peg_p _ _ _ hp).2 hf)⟩
lemma fancy (x y:Site c)(ht:pdist y≤1): peg (x+y) p≤(2:ℝ)^p*peg x p:=by
    unfold peg; rw[← mul_pow]; have he': (pdist (x+y):ℝ) ≤ pdist x+1:=by exact_mod_cast (le_trans (pdist_triangle x y) (Nat.add_le_add_left ht _))
    apply pow_le_pow_left₀ (by positivity) -- layout broken
    linarith[Nat.cast_nonneg (α:=ℝ) (pdist x)]
noncomputable def floats (x:Cover) : Cray c →L[ℝ]Cray c:=LinearMap.toContinuousLinearMap { toFun:=fun f i=> f (i.1+wrap c x,i.2),map_smul':=fun _ _=>rfl,map_add':=fun _ _=>rfl }
def Nearby (x:Cover):Prop := ∃ a:Axis,x=step a∨ x= -(step a)
lemma wagons (h:Dart p F)(x:Cover)(ht:Nearby x): Dart p (fun c=> floats x (F c)):=by
    obtain ⟨f,hf,he⟩:=h; obtain ⟨i,hi⟩:=ht; refine ⟨f*2^p,mul_nonneg hf (by positivity),fun c e=>?_⟩
    rw [mul_assoc]; exact (he c (e.1+wrap c x,e.2)).trans (mul_le_mul_of_nonneg_left (fancy e.1 _ (flipT (c:=c) x i hi).1) hf)
open Beacon.Verse
lemma listen (T:Taper)(g:su.Color)(X:Labels.Taylor su j): Dart (j+1) (fun c=>fling (c:=c) g T X):=by
    let r:= j+1; let f:= ‖g‖*‖X.val‖; refine ⟨f*2^r,mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity),fun c e=>?_⟩
    let b:= Lattice.lift e.1; let m:= 1+(pdist e.1:ℝ); have hv t (ht:t∈Set.Icc 0 (1:ℝ)): ‖wake e t‖≤ 2*m:=by
         unfold wake; apply (norm_add_le ..).trans; rw [norm_smul,basis_norm, mul_one, Real.norm_of_nonneg ht.1]; unfold m; linarith [position_norm c e.1,ht.2]
    have hp t(ht:t∈ Set.Icc 0 (1:ℝ)): ‖tinge g T X e t‖ ≤ f*2^r*peg e.1 r:=by
        unfold tinge; rw [norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (show ‖sailT T e t‖≤1 by unfold sailT; rw [Real.norm_of_nonneg (T.interval _).1]; exact (T.interval _).2)).trans
        let x:=wake e t; let V:= X.val e.2; have hh:‖Tensor.diagonal V x‖ ≤ ‖X.val‖ * ( (2*m)^r):=by apply (V.le_opNorm (fun _=>x)).trans; simp only [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul (norm_le_pi_norm ..) (pow_le_pow_left₀ (norm_nonneg _) (hv _ ht) _) (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
        rw [Real.norm_eq_abs]; refine (abs_real_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq ?_); unfold f peg; rw[mul_pow]; change _= _*m^r; ring
    exact (intervalIntegral.norm_integral_le_of_norm_le_const fun t ht=>hp t (Set.Ioc_subset_Icc_self (by simpa using ht))).trans_eq (by simp [r])
noncomputable abbrev lit (v:Site c):= vector (Lattice.lift v)
lemma frost (P:E4→ℝ)(h:∀ t:E4,‖P t‖≤ a*(1+‖t‖)^p)(ha:0≤a) : Dart p (fun c=> glaze (fun i:Site c=> P (lit i))):=by
    let F:=a*(2:ℝ)^p; have hf:0≤F:=mul_nonneg ha (by positivity); refine ⟨F+F*2^p,add_nonneg hf (mul_nonneg hf (by positivity)),fun c e=>?_⟩
    let x:=e.1; let y:=x+step e.2; have hu(u: Site c): ‖P (lit u)‖ ≤ F*peg u p:=by
        unfold F; rw [mul_assoc]; apply (h (lit u)).trans; apply mul_le_mul_of_nonneg_left _ ha; unfold peg; rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity); unfold lit; linarith [position_norm c u]
    apply (norm_sub_le ..).trans; rw [add_mul,add_comm (F*_)]; refine add_le_add ((hu y).trans ?_) (hu x); rw [mul_assoc F]; exact mul_le_mul_of_nonneg_left (fancy x _ (pdist_step ..)) hf
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.listen
#print axioms YM.Massive.Patria.Gall.frost
