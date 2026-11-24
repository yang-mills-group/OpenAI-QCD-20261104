import YM.QCD.Land.Inside

/-!
# Local gauge groups and projection of tests
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Land
open Lattice Wilson Grass Lat RP MeasureTheory Function Finset
open scoped BigOperators Matrix.Norms.Frobenius Matrix Topology
variable {n : Side} {D S : Lot} {F : ℕ}

section
variable {X A B : Type*} [Fintype X] [DecidableEq X] [Fintype A] [Fintype B]
def circuit (k : X → su.El) (F : ℕ) := copies F (rides (Equiv.refl X) fun i => touch (colour (k i)))
def turnin (k : X → su.El) (F : ℕ) := adapter (circuit k F) (Twist (circuit k F))
lemma circuits (k l : X → su.El) : circuit (k*l) F=circuit k F*circuit l F := by
  unfold circuit; rw [← copies_mul,ride_mul]; simp_rw [touch_mul,Equiv.refl_apply,Equiv.refl_trans]
  simp only [Pi.mul_apply,colour_mul]
lemma circuit_one (F : ℕ) : circuit (1 : X → su.El) F=1 := by simp [circuit,colour1,touch_one,ridden]
lemma turning (k l : X → su.El) (x : Press X F) : turnin l F (turnin k F x)=turnin (k*l) F x := by unfold turnin; rw [adapt_together,circuits,twist_mul]
lemma turnin_one (x : Press X F) : turnin 1 F x=x := by simp [turnin,circuit_one,Twist]

lemma at_psi (x : X) (i : Wind F) (k : X→su.El) :
    turnin k F (psi (place x i))=∑ j : Wind F,copies F (touch (colour (k x))) i j • psi (place x j) := by
  unfold turnin circuit; rw [adapt_psi,placed_sum,sum_eq_single x]; · simp only [placed,Equiv.refl_apply,if_true]
  · intro z _ hz; simp [placed, Ne.symm hz]
  simp
lemma at_bar (x : X) (i : Wind F) (k : X→su.El) : turnin k F (bar (place x i))=
    ∑ j : Wind F, star (copies F (touch (colour (k x))) i j) • bar (place x j) := by
  unfold turnin circuit; rw [adapt_bar,placed_sum,sum_eq_single x]; · simp only [Twist,Matrix.transpose_apply,Matrix.conjTranspose_apply,placed, Equiv.refl_apply,if_true]
  · intro z _ hz; simp [Twist,placed,Ne.symm hz]
  simp
lemma turn_pass {Y : Type*} [Fintype Y] [DecidableEq Y] (u : X → Y) (k : Y → su.El) (x : Press X F) :
    turnin k F (pass (fun i => ((u i.1.1,i.1.2),i.2)) x)=pass (fun i => ((u i.1.1,i.1.2),i.2)) (turnin (fun i => k (u i)) F x) := by
  let z : (X × Fiber) × Flavor F → (Y × Fiber) × Flavor F := fun i => ((u i.1.1,i.1.2),i.2)
  apply AlgHom.congr_fun (φ₁ := (turnin k F).comp (pass z)) (φ₂ := (pass z).comp (turnin (fun i => k (u i)) F))
  apply ext_atoms; rintro (⟨⟨x,i⟩,j⟩|⟨⟨x,i⟩,j⟩)
  · change turnin k F (pass z (psi (place x (i,j))))= pass z (turnin _ F (psi (place x (i,j))))
    rw [pass_psi, show z (place x (i,j))=place (u x) (i,j) from rfl, at_psi, at_psi,map_sum]; simp only [map_smul,pass_psi]; rfl
  change turnin k F (pass z (bar (place x (i,j))))= pass z (turnin _ F (bar (place x (i,j))))
  rw [pass_bar,show z (place x (i,j))=place (u x) (i,j) from rfl,at_bar,at_bar,map_sum]; simp only [map_smul,pass_bar]; rfl

lemma change_c : Continuous (fun p : Matrix A B ℂ × Alg A => changeVars p.1 p.2) := by
  let f (v : List A) := (List.map atom v).prod
  have hi (s : Finset A) : Continuous (fun p : Matrix A B ℂ => changeVars p (mono s)) := by
    obtain ⟨w,-,-,H⟩ := expression s
    simp_rw [H,map_list_prod,List.map_ofFn];
    let W := List.ofFn w
    have ht (l : List A) : Continuous fun p : Matrix A B ℂ => changeVars p (f l) := by
      induction l with
      | nil => simp [f]; exact continuous_const
      | cons a l ih =>
        simp_rw [show f (a::l)=atom a*f l from rfl,map_mul,change_atom]
        fun_prop
    convert ht W using 1
    ext1 M; simp only [f,W,map_list_prod,List.map_map,List.map_ofFn,Function.comp_def]
  have he (p : Matrix A B ℂ × Alg A) : changeVars p.1 p.2=∑ s : Finset A,coef s p.2 • changeVars p.1 (mono s) := by
    simp_rw [← map_smul (changeVars _),← map_sum,write]
  simp_rw [he]; exact continuous_finsetSum _ fun s _ => (Grass.continuous_coef s |>.comp continuous_snd).smul ((hi s).comp continuous_fst)

@[fun_prop] lemma turn_c : Continuous (fun p : (X → su.El) × Press X F => turnin p.1 F p.2) := by
  have he : Continuous fun k : X → su.El => circuit k F := by unfold circuit; apply (continuous_copies _).comp; apply ride_c; intro i; fun_prop
  have hb : Continuous fun k : X → su.El => Matrix.fromBlocks (circuit k F) 0 0 (Twist (circuit k F)) := by
    apply continuous_pi; rintro (i|i) <;> apply continuous_pi <;> rintro (j|j)
    all_goals simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,Twist, Matrix.transpose_apply,Matrix.conjTranspose_apply]; fun_prop
  have ht := (change_c (A:=Pairs ((X × Fiber) × Flavor F)) (B:=Pairs ((X × Fiber) × Flavor F))).comp (hb.prodMap (continuous_id (X:=Press X F)))
  exact ht
end

abbrev Town (D : Lot) := Court D → su.El
instance (D : Lot) : BorelSpace (Town D) := by unfold Town; infer_instance
instance (D : Lot) : CompactSpace (Town D) := by unfold Town; infer_instance

def stain (k : Town D) (U : Trace D) (i : Pipe D) : su.El := k (inlet i)*U i*(k (drain i))⁻¹
@[fun_prop] lemma stain_cont : Continuous (fun p : Town D × Trace D => stain p.1 p.2) := by unfold stain; fun_prop
lemma stains (k l : Town D) (U : Trace D) : stain k (stain l U) = stain (k*l) U := by ext1 i; simp [stain,mul_assoc]
lemma stain_one (U : Trace D) : stain 1 U=U := by ext1 i; simp [stain]

def stainX (k : Town D) (x : Cyl D F) : Cyl D F := ⟨fun U => turnin k F (x (stain k U)),by
  have he := stain_cont (D:=D) |>.comp (show Continuous (fun i : Trace D => (k,i)) from by fun_prop)
  have hx := (turnin k F).toLinearMap.continuous_of_finiteDimensional.comp (x.continuous.comp he)
  exact hx⟩
@[simp] lemma stain_app (k : Town D) (x : Cyl D F) (U) : stainX k x U=turnin k F (x (stain k U)) := rfl
lemma stained (k l : Town D) (x : Cyl D F) : stainX k (stainX l x)=stainX (l*k) x := by ext1 U; simp only [stain_app,turning,stains]
@[fun_prop] lemma staining_cont (x : Cyl D F) : Continuous fun k : Town D => stainX k x := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have ht : Continuous (Prod.fst : Town D × Trace D → Town D) := continuous_fst
  have hh := (turn_c (X:=Court D) (F:=F)).comp (ht.prodMk (x.continuous.comp (stain_cont (D:=D))))
  exact hh

def Neutral (x : Cyl D F) := ∀ k, stainX k x=x
lemma neutral_id {x : Cyl D F} (h : Neutral x) (k : Town D) (U) : turnin k F (x (stain k U))=x U := congrArg (fun y : Cyl D F => y U) (h k)
lemma issue_turn (x : Cyl D F) (k : Frame n) : transform k (issue n x)=issue n (stainX (fun i => k (wrap n i.val)) x) := by
  ext1 U
  have he : wraps (D:=D) n (gauge k U)= stain (D:=D) (fun i => k (wrap n i.val)) (wraps n U) := by funext i; unfold wraps Lattice.gauge stain; rw [← drains_wrap n]; rfl
  change slots F k (issue n x (gauge k U))=_; simp only [issued,he,stain_app]
  exact turn_pass (fun i : D => wrap n i.val) k _
lemma issue_inv {x : Cyl D F} (h : Neutral x) : Invariant (issue n x) := fun k => by rw [issue_turn,h]

lemma turn_bound (D : Lot) (F : ℕ) : ∃ A : ℝ, 0≤A ∧ ∀ (k : Town D) (x : Poly D F), ‖turnin k F x‖ ≤ A*‖x‖ := by
  -- bound entry sum over all monomials and Haar
  let f := fun k : Town D => ∑ s : Finset (Pairs (Pad D F)), ‖turnin k F (mono s)‖
  have hi (s : Finset (Pairs (Pad D F))) : Continuous (fun k : Town D => ‖turnin k F (mono s)‖) := by
    have hw : Continuous fun k : Town D => (k,mono s) := continuous_id.prodMk continuous_const
    have hu := (turn_c (X:=Court D) (F:=F)).comp hw
    exact Continuous.norm hu
  obtain ⟨A,hA⟩ := (continuous_finsetSum _ fun i _ => hi i).bounded_above_of_compact_support
    (HasCompactSupport.of_compactSpace f)
  refine ⟨A,(norm_nonneg _).trans (hA 1),fun k x => ?_⟩
  conv_lhs => rw [← write x,map_sum]
  refine (norm_sum_le _ _).trans ?_; rw [mul_comm A,norm_def x,sum_mul]; apply sum_le_sum
  intro i _; rw [map_smul,norm_smul]; gcongr
  apply le_trans (single_le_sum (f:=fun s => ‖turnin k F (mono (s:Finset (Pairs (Pad D F))))‖) (fun i _ => norm_nonneg _) (mem_univ i))
  exact (Real.le_norm_self _).trans (hA _)

def towns (D : Lot) := Measure.pi fun _ : Court D => su.probHaar
instance : IsProbabilityMeasure (towns D) := by unfold towns; infer_instance

def council (x : Cyl D F) : Cyl D F := ∫ k, stainX k x ∂towns D

lemma stain_pay (x : Cyl D F) : Integrable (fun k => stainX k x) (towns D) :=
  (staining_cont x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def stain_lin (F) (k : Town D) : Cyl D F →ₗ[ℂ] Cyl D F where
  toFun := stainX k
  map_smul' _ _ := by ext1 i; simp -- check
  map_add' _ _ := by ext1 i; simp

lemma stain_cost (D : Lot) (F : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ (k : Town D) (x : Cyl D F), ‖stainX k x‖ ≤ A * ‖x‖ := by
  obtain ⟨A,hp,H⟩ := turn_bound D F
  refine ⟨A,hp,fun k x => ?_⟩
  exact (ContinuousMap.norm_le _ (by positivity)).mpr fun i => (H k _).trans (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm x _) hp)
lemma council_cost (D : Lot) (F : ℕ) : ∃ A : ℝ, 0≤A ∧ ∀ x : Cyl D F, ‖council x‖ ≤ A * ‖x‖ := by
  obtain ⟨A,hp,H⟩ := stain_cost D F
  exact ⟨A,hp,fun x => (norm_integral_le_of_norm_le (integrable_const (μ:=towns D) (A*‖x‖)) (Filter.Eventually.of_forall fun i => H _ _)).trans (by simp)⟩
lemma council_stains (x : Cyl D F) : Neutral (council x) := by
  intro k; obtain ⟨A,-,H⟩ := stain_cost D F
  let L := LinearMap.mkContinuous (stain_lin F k) A (H k)
  have he := L.integral_comp_comm (stain_pay x)
  change (∫ i, stainX k (stainX i x) ∂towns D) = stainX k (council x) at he
  rw [← he]; simp_rw [stained]
  have hu : MeasurePreserving (fun i : Town D => i*k) (towns D) (towns D) :=
    measurePreserving_pi _ _ (f:= fun i (g : su.El) => g*k i) (fun i => measurePreserving_mul_right _ _)
  have hv := integral_map hu.aemeasurable (f:=fun k => stainX k x) (by rw [hu.map_eq]; exact (stain_pay x).aestronglyMeasurable)
  rw [hu.map_eq] at hv; exact hv.symm

lemma council_id {x : Cyl D F} (h : Neutral x) : council x=x := by simp_rw [council,(show ∀ k, stainX k x=x from h)]; simp

variable (C : Lat.Cut n F)
def tally (D : Lot) : Cyl D F →ₗ[ℂ] ℂ where
  toFun x := C.average (issue n x)
  map_add' x y := by rw [issue_add,map_add]
  map_smul' x y := by rw [issue_smul,map_smul]; rfl
@[simp] lemma tallying (x : Cyl D F) : tally C D x=C.average (issue n x) := rfl
lemma issued_stained (x : Cyl D F) (h : Fits n D) (k : Town D) : tally C D (stainX k x)= tally C D x := by
  let s : Court D → Site n := fun i => wrap n i.val
  let V : Frame n := Function.extend s k 1
  have hv : Injective s := fun i j H => Subtype.ext (h i.property j.property H)
  have hp : issue n (stainX k x)= transform V (issue n x) := by
    rw [issue_turn]; congr 2; exact funext fun i => (hv.extend_apply ..).symm
  simp only [tallying,hp,Lat.Cut.average, LinearMap.smul_apply, invariant_raw]
lemma tally_c (D : Lot) (h : Fits n D) (hb : 0≤C.β) : Continuous (tally C D) := by
  let a := (((101+|C.m|)^(12*F))^(sites n))
  have H (x : Cyl D F) : ‖C.raw (issue n x)‖ ≤ a*‖x‖ := (C.test_price hb (issue n x)).trans
    (mul_le_mul_of_nonneg_left (issue_price h x) (by positivity))
  refine (LinearMap.mkContinuous (tally C D) (‖(C.partitionR:ℂ)⁻¹‖*a) ?_).continuous
  intro x
  change ‖(C.partitionR:ℂ)⁻¹*C.raw _‖ ≤ _; rw [norm_mul,mul_assoc]; gcongr; exact H _
lemma council_tally (x : Cyl D F) (h : Fits n D) (hb : 0≤C.β) : tally C D (council x)=tally C D x := by
  let f : Cyl D F →L[ℂ] ℂ := ⟨tally C D,tally_c C D h hb⟩
  have he := f.integral_comp_comm (stain_pay x)
  change (∫ k, tally C D (stainX k x) ∂towns D)=tally C D (council x) at he -- check direction
  rw [← he]; simp_rw [issued_stained C x h]; simp
end YM.QCD.Land
